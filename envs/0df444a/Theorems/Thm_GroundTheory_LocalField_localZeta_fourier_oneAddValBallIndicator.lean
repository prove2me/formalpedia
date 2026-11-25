-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_fourier_oneAddValBallIndicator
-- name    : GroundTheory.LocalField.localZeta_fourier_oneAddValBallIndicator
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:09.46972+00:00
-- url     : https://prove2.me/theorems/fae4c95b-4bbd-51e8-adbb-6c427e00b5be
-- title:
--   Local Field: local Zeta fourier one Add Val Ball Indicator
-- statement:
--   The Local Field construction uses the local Zeta fourier one Add Val Ball Indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L363-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L363-L464

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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ

theorem GroundTheory.LocalField.localZeta_fourier_oneAddValBallIndicator (hr : ¬ IsUnramifiedChar χ) {s : ℂ}
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta (localFourier (selfDualMeasure ψ) ψ (oneAddValBallIndicator (quasiCharConductor χ)))
        χ⁻¹ (1 - s) =
      localEpsilon χ ψ s * localZeta (oneAddValBallIndicator (quasiCharConductor χ)) χ s := by sorry
