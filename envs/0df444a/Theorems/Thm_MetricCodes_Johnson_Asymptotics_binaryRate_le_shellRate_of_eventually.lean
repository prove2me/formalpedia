-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Asymptotics_binaryRate_le_shellRate_of_eventually
-- name    : MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/bbfcb030-e6f7-4364-b15a-b643f744a398
-- title:
--   MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
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

theorem MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
          C * bassalygoWindowFibreQuotient a b g u n) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.shellRate a b g u := by sorry
