-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lintegral_multHaar
-- name    : GroundTheory.LocalField.lintegral_multHaar
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:27.812576+00:00
-- url     : https://prove2.me/theorems/70bb9ab9-3ad9-5bfe-baab-aef609237bd6
-- title:
--   Local Field: lintegral mult Haar
-- statement:
--   The Local Field construction uses the lintegral mult Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L164-L172

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
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

theorem GroundTheory.LocalField.lintegral_multHaar {g : K → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂(multHaar K) =
      multHaarConst K * ∫⁻ x in {0}ᶜ, ((modulus x : ℝ≥0∞))⁻¹ * g x ∂(haarIntegers K) := by sorry
