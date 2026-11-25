-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_exists_sphere
-- name    : GlobalTheory.ThetaGauss.exists_sphere
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:06.81588+00:00
-- url     : https://prove2.me/theorems/384a5029-e460-4164-a80d-ff510caa877a
-- title:
--   Theta Gauss: exists sphere
-- statement:
--   The Theta Gauss construction uses the exists sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L188-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L188-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}

theorem GlobalTheory.ThetaGauss.exists_sphere {p : ℂ → Prop} (hp : ∀ᶠ t in 𝓝[≠] (0 : ℂ), p t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ t ∈ sphere (0 : ℂ) r, p t := by sorry
