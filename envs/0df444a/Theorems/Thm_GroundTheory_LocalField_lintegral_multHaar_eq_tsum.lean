-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lintegral_multHaar_eq_tsum
-- name    : GroundTheory.LocalField.lintegral_multHaar_eq_tsum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:43.128411+00:00
-- url     : https://prove2.me/theorems/5693331e-31e1-530e-9b40-07ef7a0de760
-- title:
--   Local Field: lintegral mult Haar eq tsum
-- statement:
--   The Local Field construction uses the lintegral mult Haar eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L138-L141

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]

theorem GroundTheory.LocalField.lintegral_multHaar_eq_tsum (g : Kˣ → ℝ≥0∞) :
    ∫⁻ u, g u ∂multHaar K = ∑' k : ℤ, ∫⁻ u in ordShell K k, g u ∂multHaar K := by sorry
