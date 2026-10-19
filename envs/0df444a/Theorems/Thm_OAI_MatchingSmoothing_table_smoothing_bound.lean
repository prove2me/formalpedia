-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_table_smoothing_bound
-- name    : OAI.MatchingSmoothing.table_smoothing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:45:47.158819+00:00
-- url     : https://prove2.me/theorems/23ceb039-89cd-4652-842b-d6104959841b
-- title:
--   Color-table class averages of high-degree functions on perfect matchings have small energy
-- statement:
--   Fix $h\in\mathbb N$, the vertex set $V_h=\{0,\dots,h-1\}\times\{0,1\}$ with $2h$ elements, and the finite set $\mathcal M_h$ of perfect matchings of $V_h$, encoded as fixed-point-free involutions $M$ of $V_h$. Let $\mathcal P_d\subseteq\mathbb R^{\mathcal M_h}$ be the span of all products of at most $d$ edge indicators $x_{(u,v)}(M)=\mathbf 1[M(u)=v]$ (including the constant $1$), and use the inner product $\langle f,g\rangle=\sum_Mf(M)g(M)$ on $\mathbb R^{\mathcal M_h}$.
--
--   For a coloring $z:V_h\to\{0,1,2\}$ and a matching $M$, the *color table* $\operatorname{tab}_z(M)$ records, for each of the six unordered color pairs $\{a,b\}$ (with $a=b$ allowed), the number of edges of $M$ whose endpoints have colors $a$ and $b$. Let $S$ be the standard matching that pairs $(i,0)$ with $(i,1)$ for every $i$.
--
--   Let $k\in\mathbb N$ with $4k<h$, and let $f_0:V_h\to\{0,1,2\}$ be a coloring that uses every color, i.e. $|f_0^{-1}(c)|>0$ for $c=0,1,2$. Put $\tau=\operatorname{tab}_{f_0}(S)$, and let $\mathcal C$ be the set of colorings $z:V_h\to\{0,1,2\}$ with the same color-class sizes as $f_0$, i.e. $|z^{-1}(c)|=|f_0^{-1}(c)|$ for every $c$. For $f:\mathcal M_h\to\mathbb R$ and $z\in\mathcal C$ let
--
--   $$
--   \bar f(z)=\frac{1}{|\{M\in\mathcal M_h:\operatorname{tab}_z(M)=\tau\}|}\sum_{M\in\mathcal M_h:\ \operatorname{tab}_z(M)=\tau}f(M)
--   $$
--
--   be the average of $f$ over the matchings whose $z$-table equals $\tau$. Let $a\ge0$ be a real number with $(h+1)^{33}\le\binom hk a^2$. Then for every $f\in\mathbb R^{\mathcal M_h}$ orthogonal to $\mathcal P_{16k^2}$,
--
--   $$
--   \frac{1}{|\mathcal C|}\sum_{z\in\mathcal C}\bar f(z)^2\;\le\;a\cdot\frac{1}{|\mathcal M_h|}\sum_{M\in\mathcal M_h}f(M)^2 .
--   $$
--
--   In words: if $f$ has no component of degree at most $16k^2$ in the edge indicators, then averaging $f$ over a color-table class, for a uniformly random coloring with prescribed class sizes, shrinks its mean square by the factor $a$; the smallest admissible choice is $a=(h+1)^{33/2}\binom hk^{-1/2}$. This is the basic quantitative estimate behind the uniform smoothing bounds for table averages.
--
--   **Formalization Note** $\bar f(z)$ is `fiberAverage (tableRelation f₀) f z`, a sum divided by the size of the class (Lean's convention $x/0=0$ would apply to an empty class, but the classes here are nonempty). The table is `Pairing.table`, which counts the vertices $v$ whose color pair $(z(v),z(M(v)))$ has a given unordered type and halves the count. $\tau$ is `threeTable f₀`, $\mathcal C$ is `Colorings (Vertices h) (Fin 3) (histogram f₀)`, and the degree is written `(4*k)*(4*k)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/FiberAverages.lean#L87-L121

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3
open Matrix
attribute [local instance] Classical.propDecidable
open scoped RealInnerProductSpace

theorem OAI.MatchingSmoothing.table_smoothing_bound {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (f₀ : Vertices h → Fin 3) (hf₀ : ∀ i, 0 < histogram f₀ i)
    (a : ℝ) (ha : 0 ≤ a) (hHa : (h+1 : ℝ)^33 ≤ (h.choose k : ℝ) * a^2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
    a * ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by sorry
