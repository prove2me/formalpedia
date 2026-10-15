-- Prove2me | Theorems.Thm_OAI_ForestSpace_exists_raw_test
-- name    : OAI.ForestSpace.exists_raw_test
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:11.761465+00:00
-- url     : https://prove2.me/theorems/dae63503-31fa-422f-94df-e7f110052b72
-- title:
--   Dual norms are approached from below by evaluations on finitely supported vectors of norm at most one
-- statement:
--   Let $V$ be a partially ordered set, let $c_{00}(V)$ be the space of finitely supported functions $V\to\mathbb{R}$ with the disjoint-segment norm, let $J(V)$ be its completion and $\iota:c_{00}(V)\to J(V)$ the canonical isometric embedding, and let $J(V)^*$ be the full continuous dual of $J(V)$ with the operator norm.
--
--   **Theorem.** Let $x\in J(V)^*$ and $r\in\mathbb{R}$ with $r<\|x\|$. Then there is a finitely supported $u\in c_{00}(V)$ with $\|u\|\le1$ and
--   $$
--   r<x(\iota u) .
--   $$
--
--   So the norm of a dual element can be approached by evaluations on finitely supported vectors of norm at most one, and the pairing itself, not merely its absolute value, can be made to exceed $r$. In the dual estimate for the forest space this supplies the finitely supported vectors $f$ and $k$ that nearly norm the two dual components before they are corrected.
--
--   **Formalization Note** The vector $u$ is a `TestVector V`, and $\iota u$ is its coercion into the completion `J V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Polar.lean#L36-L50

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.exists_raw_test (x : FullDual V) {r : ℝ} (hr : r < ‖x‖) :
    ∃ u : TestVector V, ‖u‖ ≤ 1 ∧ r < x (u : J V) := by sorry
