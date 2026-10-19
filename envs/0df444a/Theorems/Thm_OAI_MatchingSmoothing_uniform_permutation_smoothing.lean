-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_uniform_permutation_smoothing
-- name    : OAI.MatchingSmoothing.uniform_permutation_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:57:11.483257+00:00
-- url     : https://prove2.me/theorems/b7c8aa5f-684d-4788-92c1-7ee6835c9292
-- title:
--   Permutation-averaged decay of color-table class averages of high-degree residuals
-- statement:
--   For $h\in\mathbb N$ let $V_h=\{0,\dots,h-1\}\times\{0,1\}$ (a set of $2h$ vertices), let $\mathcal M_h$ be the set of perfect matchings of $V_h$, encoded as fixed-point-free involutions, and let $\mathfrak S(V_h)$ be the group of all permutations of $V_h$; a permutation $p$ relabels a matching $M$ as $pMp^{-1}$. Let $\mathcal P_d$ be the span of all products of at most $d$ edge indicators $x_{(u,v)}(M)=\mathbf 1[M(u)=v]$ (including the constant $1$), and let $L_d$ be the orthogonal projection of $\mathbb R^{\mathcal M_h}$ onto $\mathcal P_d$ with respect to $\langle f,g\rangle=\sum_Mf(M)g(M)$. For a coloring $z:V_h\to\{0,1,2\}$ the color table $\operatorname{tab}_z(M)$ records, for each of the six unordered color pairs $\{a,b\}$ ($a=b$ allowed), the number of edges of $M$ with endpoint colors $a$ and $b$.
--
--   **Theorem.** For every $K\in\mathbb N$ there exist $d,H\in\mathbb N$ with $d\ge1$ such that for every $h\ge H$, every coloring $z:V_h\to\{0,1,2\}$ that uses all three colors, every perfect matching $M_0$ of $V_h$ and every function $f:\mathcal M_h\to\mathbb R$, writing $r=f-L_df$,
--
--   $$
--   \mathbb E_{p}\Big[\Big(\mathbb E_{M:\ \operatorname{tab}_z(M)=\operatorname{tab}_z(M_0)}\;r(pMp^{-1})\Big)^2\Big]\;\le\;(2h)^{-2K}\;\mathbb E_{M}\big[f(M)^2\big].
--   $$
--
--   Here $p$ is uniform on $\mathfrak S(V_h)$, the inner expectation is the uniform average over the matchings $M$ with $\operatorname{tab}_z(M)=\operatorname{tab}_z(M_0)$, and $\mathbb E_M$ is the uniform average over $\mathcal M_h$.
--
--   This is the coloring-averaged smoothing bound rewritten as an average over relabellings of the vertex set, for a fixed coloring and a fixed target class. It is the form needed when the available symmetries come from permutations acting on the vertices. The degree $d$ depends only on $K$.
--
--   **Formalization Note** $L_df$ is `lowProjection h d f`, the inner average is `predicateAverage (fun M => M.table z = M₀.table z)`, and the outer averages are Mathlib's uniform expectations over the finite types `Equiv.Perm (Vertices h)` and `Pairing (Vertices h)`. The factor $(2h)^{-2K}$ is `((2*h : ℝ)^(2*K))⁻¹`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PermutationSmoothing.lean#L102-L125

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

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingSmoothing.uniform_permutation_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (z : Vertices h → Fin 3), (∀ i, 0 < histogram z i) →
      ∀ (M₀ : Pairing (Vertices h)) (f : Pairing (Vertices h) → ℝ),
      (𝔼 p : Equiv.Perm (Vertices h),
        (predicateAverage (fun M => M.table z = M₀.table z)
          (fun M => (f - lowProjection h d f) (Pairing.relabel p M)))^2) ≤
      ((2*h : ℝ)^(2*K))⁻¹ * (𝔼 M, (f M)^2) := by sorry
