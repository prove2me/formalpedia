-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_collision_rate_tendsto
-- name    : OAI.PiExponent.finite_collision_rate_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T03:58:09.08592+00:00
-- url     : https://prove2.me/theorems/65abe21a-2a95-49ce-b400-e091693d8443
-- title:
--   Finite weighted-simplex collision rates have the stated volume limit
-- statement:
--   For fixed positive weights ceil(log q_i), the ratio of the strict (m+1)-dimensional row count to H times the weak m-dimensional low-index count tends to the quotient of their simplex volumes. The collision prefactor is unchanged, A may be any positive real, and eta may be any real.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.finite_collision_rate_tendsto
    (m K : ℕ) (v0 theta : ℚ) (A eta : ℝ) (q : Fin m → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto
      (OAI.PiExponent.FiniteMinorComparison.collisionRate
        K (v0 : ℝ) (theta : ℝ) A eta q) atTop
      (𝓝 (OAI.PiExponent.FiniteMinorComparison.collisionLimit
        m K (v0 : ℝ) (theta : ℝ) A eta)) := by sorry
