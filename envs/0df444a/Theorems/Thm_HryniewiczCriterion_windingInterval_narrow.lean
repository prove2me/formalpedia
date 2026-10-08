-- Prove2me | Theorems.Thm_HryniewiczCriterion_windingInterval_narrow
-- name    : HryniewiczCriterion.windingInterval_narrow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T22:16:09.142872+00:00
-- url     : https://prove2.me/theorems/d2360900-5ddf-4eb3-838e-b79a330796f4
-- title:
--   The winding set of a normalized symplectic plane path is a narrow closed interval
-- statement:
--   For a smooth determinant-one plane path starting at the identity, its winding set is a nonempty closed interval $[a,b]$ with $b-a<1/2$. Endpoint degeneracy is allowed.
-- source:
--   Hryniewicz, https://arxiv.org/html/1105.2077v5#S2.SS1.SSS1, Section 2.1.1, pp. 5–6, the winding interval and equations (4)–(5).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.windingInterval_narrow (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : ContDiffOn ℝ ∞ (fun t i j => φ t i j) (Set.Icc 0 1))
    (hsymp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1)
    (h0 : φ 0 = 1) :
    ∃ a b : ℝ, a ≤ b ∧ windingInterval φ = Set.Icc a b ∧ b - a < 1 / 2 := by sorry
