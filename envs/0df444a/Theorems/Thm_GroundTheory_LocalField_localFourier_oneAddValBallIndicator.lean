-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localFourier_oneAddValBallIndicator
-- name    : GroundTheory.LocalField.localFourier_oneAddValBallIndicator
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:59.090377+00:00
-- url     : https://prove2.me/theorems/344eb716-93dc-50bd-8376-816c78e2834d
-- title:
--   Local Field: local Fourier one Add Val Ball Indicator
-- statement:
--   The Local Field construction uses the local Fourier one Add Val Ball Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L249-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L249-L261

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

theorem GroundTheory.LocalField.localFourier_oneAddValBallIndicator (μ : Measure K) [μ.IsAddHaarMeasure]
    {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (c : ℤ) (y : K) :
    localFourier μ ψ (oneAddValBallIndicator c) y =
      (ψ y : ℂ) * ((μ.real (valBall K c) : ℂ) *
        (valBall K (addCharConductor ψ - c) : Set K).indicator (fun _ => 1) y) := by sorry
