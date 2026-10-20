-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
-- name    : MetricCodes.Johnson.Asymptotics.eventually_admissibleDegrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:24.606098+00:00
-- url     : https://prove2.me/theorems/c83354d7-18f5-4071-9b3f-60a29343ca18
-- title:
--   MetricCodes.Johnson.Asymptotics.eventually_admissibleDegrees
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics

theorem MetricCodes.Johnson.Asymptotics.eventually_admissibleDegrees
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      MetricCodes.Johnson.AdmissibleDegrees n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n)
        (terminalDegree u n) := by sorry
