-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integral_multHaar
-- name    : GroundTheory.LocalField.integral_multHaar
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:13.645976+00:00
-- url     : https://prove2.me/theorems/077dbec5-e7bd-45a5-b1d1-c80950a6a894
-- title:
--   Local Field: integral mult Haar
-- statement:
--   The Local Field construction uses the integral mult Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L174-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean#L174-L186

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

theorem GroundTheory.LocalField.integral_multHaar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : K → E) :
    ∫ u, f u ∂(multHaar K) =
      (multHaarConst K).toReal • ∫ x in {0}ᶜ, ((modulus x : ℝ))⁻¹ • f x ∂(haarIntegers K) := by sorry
