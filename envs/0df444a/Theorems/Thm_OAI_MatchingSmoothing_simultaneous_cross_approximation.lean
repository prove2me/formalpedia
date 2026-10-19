-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_simultaneous_cross_approximation
-- name    : OAI.MatchingSmoothing.simultaneous_cross_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:02:08.291659+00:00
-- url     : https://prove2.me/theorems/1f37ec99-a577-4883-b0e4-72ce1609a6e4
-- title:
--   Simultaneous low-degree approximation of crossing-profile averages for covariant families
-- statement:
--   A *pairing* of a finite set $V$ is a perfect matching of $V$, viewed as a fixed-point-free involution $N\colon V\to V$; write $\mathcal P(V)$ for the finite set of pairings. A permutation $p$ of $V$ acts on pairings by relabelling, $N\mapsto pNp^{-1}$. For a coloring $z\colon V\to\{0,1,2\}$ the *cross vector* of a pairing $N$ is
--   $$X_z(N)=\bigl(N_{01},\,N_{02},\,N_{12}\bigr)\in\mathbb{R}^3,\qquad N_{ab}=\#\{v\in V:\ z(v)=a,\ z(N(v))=b\},$$
--   so $N_{ab}$ is the number of edges of $N$ joining the color classes $a$ and $b$. For a function $\phi$ on $\mathcal P(V)$ and a pairing $M$, let $\operatorname{avg}_{X_z(N)=X_z(M)}\phi(N)$ denote the arithmetic mean of $\phi$ over all pairings $N$ with the same cross vector as $M$. A function $P\colon\mathbb{R}^3\to\mathbb{R}$ has *degree at most $d$* if it is a linear combination of products $v_{c_1}v_{c_2}\cdots v_{c_k}$ of at most $d$ coordinates ($0\le k\le d$, the empty product being $1$), i.e. a real polynomial of total degree at most $d$.
--
--   **Theorem.** For every $K\in\mathbb{N}$ there are natural numbers $d\ge1$ and $H$ with the following property. Let $h\ge H$, let $V$ be a finite set with exactly $2h$ elements, let $G$ be a finite group and let $I$, $T$ be finite index sets. For each $i\in I$ let $z_i\colon V\to\{0,1,2\}$ be a coloring that uses each of the three colors at least once, let $M_{i,t}\in\mathcal P(V)$ ($t\in T$) be pairings, let $\lambda_i$ be an arbitrary map from the symmetric group $\mathrm{Sym}(V)$ to $G$, and let $g_i\colon G\times\mathcal P(V)\to\mathbb{R}$ satisfy the covariance rule
--   $$g_i\bigl(a\,\lambda_i(p),\,N\bigr)=g_i\bigl(a,\,pNp^{-1}\bigr)\qquad\text{for all } a\in G,\ p\in\mathrm{Sym}(V),\ N\in\mathcal P(V).$$
--   Let $B\in\mathbb{R}$ satisfy $g_i(a,N)^2\le B^2$ for all $i,a,N$. Then there exist one group element $a\in G$ and polynomials $P_i\colon\mathbb{R}^3\to\mathbb{R}$ ($i\in I$) of degree at most $d$ such that
--   $$\sum_{i\in I}\sum_{t\in T}\Bigl(\operatorname*{avg}_{X_{z_i}(N)=X_{z_i}(M_{i,t})}g_i(a,N)\;-\;P_i\bigl(X_{z_i}(M_{i,t})\bigr)\Bigr)^2\;\le\;\frac{|I|\,|T|\,B^2}{(2h)^{2K}}.$$
--
--   For each $i$ the averaged quantity depends on the pairing $M_{i,t}$ only through its cross vector. The theorem says that, after moving to a single well-chosen group element $a$, all these fiber averages are simultaneously close, at the prescribed sample points $X_{z_i}(M_{i,t})$, to polynomials of a degree $d$ that depends only on $K$, with a mean-square error that decays like $(2h)^{-2K}$ in the number $2h$ of vertices. In the lower bound for the PSD rank of the perfect matching slack matrix it is applied with $G$ a symmetric group of a larger vertex set and with $g_i$ built from averaged entries of PSD factors, so that these entries become, up to a tiny error, low-degree polynomials in the three crossing counts.
--
--   **Formalization Note** The vertex set is any finite type `V` given with an equivalence `V ≃ Vertices h`, where `Vertices h = Fin h × Bool`; only the resulting cardinality $2h$ matters. The fiber average is `predicateAverage`, which divides by the number of pairings satisfying the predicate; here this set contains $M_{i,t}$, so no division by zero occurs. The degree condition is membership in `lowDegree (fun c v => v c) d`, the maps $\lambda_i$ are `lift i` and need not be homomorphisms, and the cross vector is `crossVector`, indexed by the color pairs $(0,1),(0,2),(1,2)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CrossSelection.lean#L9-L67

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables

open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingSmoothing.simultaneous_cross_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (V G I T : Type) [Fintype V] [Fintype G] [Group G] [Fintype I] [Fintype T]
      (_e : V ≃ Vertices h) (z : I → V → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing V)
      (lift : I → Equiv.Perm V → G)
      (g : I → G → Pairing V → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) -
            P i (crossVector (z i) (M i t)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by sorry
