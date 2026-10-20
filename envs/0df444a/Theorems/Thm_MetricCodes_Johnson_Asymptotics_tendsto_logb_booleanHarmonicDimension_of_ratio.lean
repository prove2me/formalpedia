-- Prove2me | Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_booleanHarmonicDimension_of_ratio
-- name    : MetricCodes.Johnson.Asymptotics.tendsto_logb_booleanHarmonicDimension_of_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:24.606098+00:00
-- url     : https://prove2.me/theorems/899626c7-161a-493e-b9b8-73cd37c792c1
-- title:
--   MetricCodes.Johnson.Asymptotics.tendsto_logb_booleanHarmonicDimension_of_ratio
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

theorem MetricCodes.Johnson.Asymptotics.tendsto_logb_booleanHarmonicDimension_of_ratio
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hhalf : ∀ᶠ n : ℕ in atTop, 2 * K n ≤ N n)
    (hNle : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.booleanHarmonicDimension (N n) (K n) : ℝ) /
            (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by sorry
