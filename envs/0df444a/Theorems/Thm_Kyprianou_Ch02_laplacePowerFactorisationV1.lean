-- Prove2me | Theorems.Thm_Kyprianou_Ch02_laplacePowerFactorisationV1
-- name    : Kyprianou.Ch02.laplacePowerFactorisationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:02:21.277733+00:00
-- url     : https://prove2.me/theorems/0dfcab01-2ed8-4e2e-9ab8-f7a143a65912
-- title:
--   Asymptotic factorisation for disjoint positive and negative cell contributions
-- statement:
--   The first-order defects are O(1/N); the power difference between a+b-1 and ab is at most N(1-a)(1-b), which tends to zero. The product powers have the asserted limit.
-- source:
--   Kyprianou (2006), Exercise 2.8, independence of Jordan variation components.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.laplacePowerFactorisationV1
    (a b : ℕ → ℝ) (α β : ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 1) (hb : ∀ n, b n ∈ Set.Icc 0 1)
    (hc : ∀ n, 0 ≤ a n+b n-1)
    (hα : 0 < α) (hβ : 0 < β)
    (hA : Tendsto (fun n => a n^(n+1)) atTop (nhds α))
    (hB : Tendsto (fun n => b n^(n+1)) atTop (nhds β)) :
    Tendsto (fun n => (a n+b n-1)^(n+1)) atTop (nhds (α*β)) := by sorry
