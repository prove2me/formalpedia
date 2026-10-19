-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_uniform_table_smoothing
-- name    : OAI.MatchingSmoothing.uniform_table_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:48:15.605658+00:00
-- url     : https://prove2.me/theorems/d77c010a-3563-49df-80df-d0da4f836efd
-- title:
--   Polynomial decay of color-table class averages after removing a low-degree projection
-- statement:
--   For $h\in\mathbb N$ let $V_h=\{0,\dots,h-1\}\times\{0,1\}$ (a set of $2h$ vertices) and let $\mathcal M_h$ be the set of perfect matchings of $V_h$, encoded as fixed-point-free involutions. Equip $\mathbb R^{\mathcal M_h}$ with the inner product $\langle f,g\rangle=\sum_Mf(M)g(M)$. Let $\mathcal P_d\subseteq\mathbb R^{\mathcal M_h}$ be the span of all products of at most $d$ edge indicators $x_{(u,v)}(M)=\mathbf 1[M(u)=v]$ (including the constant $1$), and let $\Pi_d$ be the orthogonal projection onto $\mathcal P_d$.
--
--   For a coloring $z:V_h\to\{0,1,2\}$ and a matching $M$, the color table $\operatorname{tab}_z(M)$ records, for each of the six unordered color pairs $\{a,b\}$ ($a=b$ allowed), the number of edges of $M$ with endpoint colors $a$ and $b$. Let $S$ be the standard matching pairing $(i,0)$ with $(i,1)$. For a coloring $f_0$ let $\mathcal C_{f_0}$ be the set of colorings with the same color-class sizes as $f_0$, and for $g:\mathcal M_h\to\mathbb R$ and $z\in\mathcal C_{f_0}$ let $\bar g(z)$ be the average of $g$ over the matchings $M$ with $\operatorname{tab}_z(M)=\operatorname{tab}_{f_0}(S)$.
--
--   **Theorem.** For every $K\in\mathbb N$ there exist $d,H\in\mathbb N$ with $d\ge1$ such that for every $h\ge H$, every coloring $f_0:V_h\to\{0,1,2\}$ that uses all three colors, and every $f\in\mathbb R^{\mathcal M_h}$,
--
--   $$
--   \frac{1}{|\mathcal C_{f_0}|}\sum_{z\in\mathcal C_{f_0}}\overline{(f-\Pi_df)}(z)^2\;\le\;(2h)^{-2K}\cdot\frac{1}{|\mathcal M_h|}\sum_{M\in\mathcal M_h}f(M)^2 .
--   $$
--
--   The degree $d$ depends only on $K$, not on $h$ or on the coloring. So after removing the projection onto polynomials of a fixed degree $d$, the mean square of the class averages is at most $(2h)^{-2K}$ times the mean square of the original function, uniformly over all colorings that use every color; any prescribed polynomial rate of decay can be reached by taking $K$ large.
--
--   **Formalization Note** $\Pi_df$ is `polynomialProjection h d f`, the `starProjection` of `f` onto `polynomialSpace h d`; the factor $(2h)^{-2K}$ is `((2*h : ℝ)^(2*K))⁻¹`; the class average is `fiberAverage (tableRelation f₀)` and $\mathcal C_{f_0}$ is `Colorings (Vertices h) (Fin 3) (histogram f₀)`. The proof takes $d=(4k)^2$ with $k=4K+34$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ScalarSmoothing.lean#L50-L70

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing

open OAI OAI.MatchingSmoothing
open Filter Asymptotics

theorem OAI.MatchingSmoothing.uniform_table_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (f₀ : Vertices h → Fin 3), (∀ i, 0 < histogram f₀ i) →
      ∀ f : MatchingSpace h,
      (∑ z, fiberAverage (tableRelation f₀)
        (matchingEquiv h (f - polynomialProjection h d f)) z ^ 2) /
        Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
      ((2*h : ℝ)^(2*K))⁻¹ *
        ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by sorry
