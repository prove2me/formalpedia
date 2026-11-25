-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_indicator_valBall
-- name    : GroundTheory.LocalField.localFourier_indicator_valBall
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:28.532009+00:00
-- url     : https://prove2.me/theorems/2888d6f0-4479-47cd-b8e6-7593368a3645
-- title:
--   Local Field: local Fourier indicator val Ball
-- statement:
--   The Local Field construction uses the local Fourier indicator val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L153-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L153-L173

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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
variable {χ : Kˣ →* ℂˣ}

theorem GroundTheory.LocalField.localFourier_indicator_valBall (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (k : ℤ) (y : K) :
    localFourier μ ψ ((valBall K k : Set K).indicator fun _ => 1) y =
      (μ.real (valBall K k) : ℂ) *
        (valBall K (addCharConductor ψ - k) : Set K).indicator (fun _ => 1) y := by sorry
