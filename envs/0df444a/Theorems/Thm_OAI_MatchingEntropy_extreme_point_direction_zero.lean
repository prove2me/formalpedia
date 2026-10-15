-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_extreme_point_direction_zero
-- name    : OAI.MatchingEntropy.extreme_point_direction_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:10:06.313541+00:00
-- url     : https://prove2.me/theorems/41f5c41a-c22d-44d0-befb-7e09c2b92c06
-- title:
--   No line through an extreme point stays in the set on both sides
-- statement:
--   Let $J$ be an arbitrary index set and let $P\subseteq\mathbb R^J$ be any set of real-valued functions on $J$. Let $x$ be an extreme point of $P$: $x\in P$, and whenever $x$ lies in the open segment between two points $x_1,x_2\in P$, then $x_1=x_2=x$. Let $u\in\mathbb R^J$ be a direction such that $x+tu\in P$ for all real $t$ in some neighbourhood of $0$. Then
--
--   $$
--   u=0 .
--   $$
--
--   In words, an extreme point admits no nonzero direction of two-sided motion inside the set. In the proof of Edmonds' perfect matching polytope theorem this is applied to an extreme point $x$ of the degree and odd-cut polytope and the direction $\mathbf 1_M-x$ given by a perfect matching in the support of $x$, which shows $x=\mathbf 1_M$.
--
--   **Formalization Note** No convexity of $P$ and no finiteness of $J$ is assumed. Extreme points are Mathlib's `Set.extremePoints ℝ P`, and the hypothesis is the filter statement `∀ᶠ t in 𝓝 0, x + t • u ∈ P`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polyhedron.lean#L60-L81

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype J] in
theorem OAI.MatchingEntropy.extreme_point_direction_zero (P : Set (J → ℝ)) {x : J → ℝ}
    (hx : x ∈ Set.extremePoints ℝ P) (u : J → ℝ)
    (hu : ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ P) : u=0 := by sorry
