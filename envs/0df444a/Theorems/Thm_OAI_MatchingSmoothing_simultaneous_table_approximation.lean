-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_simultaneous_table_approximation
-- name    : OAI.MatchingSmoothing.simultaneous_table_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:57:55.848522+00:00
-- url     : https://prove2.me/theorems/b6fbc73c-c687-4e8c-9e98-48e0f11c050a
-- title:
--   A single group element makes all color-table class averages close to low-degree polynomials
-- statement:
--   For $h\in\mathbb N$ let $V_h=\{0,\dots,h-1\}\times\{0,1\}$ (a set of $2h$ vertices), let $\mathcal M_h$ be the set of perfect matchings of $V_h$, encoded as fixed-point-free involutions, and let $\mathfrak S(V_h)$ be the group of permutations of $V_h$; a permutation $p$ relabels a matching $N$ as $pNp^{-1}$. For a coloring $z:V_h\to\{0,1,2\}$ the color table $\operatorname{tab}_z(N)=(t_{\{a,b\}})$ records, for each of the six unordered color pairs $\{a,b\}$ ($a=b$ allowed), the number of edges of $N$ with endpoint colors $a$ and $b$.
--
--   **Theorem.** For every $K\in\mathbb N$ there exist $d,H\in\mathbb N$ with $d\ge1$ such that the following holds for every $h\ge H$. Let $G$ be a finite group and let $I$ and $T$ be finite sets. For each $i\in I$ let $z_i:V_h\to\{0,1,2\}$ be a coloring that uses all three colors, and for $i\in I$, $t\in T$ let $M_{i,t}\in\mathcal M_h$. Let $\lambda_i:\mathfrak S(V_h)\to G$ $(i\in I)$ be arbitrary maps, and let $g_i:G\to\mathbb R^{\mathcal M_h}$ $(i\in I)$ satisfy the covariance condition
--
--   $$
--   g_i\big(a\,\lambda_i(p)\big)(N)=g_i(a)\big(pNp^{-1}\big)\qquad\text{for all }i\in I,\ a\in G,\ p\in\mathfrak S(V_h),\ N\in\mathcal M_h .
--   $$
--
--   Let $B\in\mathbb R$ with $g_i(a)(N)^2\le B^2$ for all $i,a,N$. Then there exist $a\in G$ and real polynomials $P_i$ $(i\in I)$ in three variables, each of total degree at most $d$, such that, writing $\tau^{i,t}=\operatorname{tab}_{z_i}(M_{i,t})$ and $\operatorname{Avg}_{i,t}$ for the uniform average over the matchings $N$ with $\operatorname{tab}_{z_i}(N)=\tau^{i,t}$,
--
--   $$
--   \sum_{i\in I}\sum_{t\in T}\Big(\operatorname{Avg}_{i,t}\,g_i(a)\;-\;P_i\big(\tau^{i,t}_{\{0,1\}},\tau^{i,t}_{\{0,2\}},\tau^{i,t}_{\{1,2\}}\big)\Big)^2\;\le\;|I|\,|T|\,(2h)^{-2K}B^2 .
--   $$
--
--   So one common element $a$ makes every class average $\operatorname{Avg}_{i,t}\,g_i(a)$ close, in mean square over the pairs $(i,t)$, to a polynomial of degree at most $d$ in the three bichromatic counts of the target table, with error at most $(2h)^{-2K}B^2$ per pair. The degree $d$ depends only on $K$. This is the selection step that produces simultaneous low-degree approximations for many local functions at once.
--
--   **Formalization Note** $G$, $I$, $T$ are types in `Type` with `Fintype` instances, $\lambda_i$ is `lift i` (not required to be a homomorphism), each $P_i$ lies in `lowDegree (fun c (v : Fin 3 → ℝ) => v c) d` and is evaluated at `fun c => (M i t).table (z i) (threeEdgeType (crossPair c))`, and the averages are `predicateAverage`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SimultaneousSmoothing.lean#L20-L68

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
open scoped BigOperators

theorem OAI.MatchingSmoothing.simultaneous_table_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (G I T : Type) [Fintype G] [Group G] [Fintype I] [Fintype T]
      (z : I → Vertices h → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing (Vertices h))
      (lift : I → Equiv.Perm (Vertices h) → G)
      (g : I → G → Pairing (Vertices h) → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => N.table (z i) = (M i t).table (z i)) (g i a) -
            P i (fun c => ((M i t).table (z i) (threeEdgeType (crossPair c)) : ℝ)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by sorry
