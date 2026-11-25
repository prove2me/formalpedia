-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_fourier_indicator_integers
-- name    : GroundTheory.LocalField.localZeta_fourier_indicator_integers
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:38.368575+00:00
-- url     : https://prove2.me/theorems/9dc50ed3-9d1d-57ea-a8aa-5c0fdb83b33d
-- title:
--   Local Field: local Zeta fourier indicator integers
-- statement:
--   The Local Field construction uses the local Zeta fourier indicator integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L183-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L183-L207

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

theorem GroundTheory.LocalField.localZeta_fourier_indicator_integers (hu : IsUnramifiedChar χ) {s : ℂ}
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta (localFourier (selfDualMeasure ψ) ψ ((valBall K 0 : Set K).indicator fun _ => 1))
        χ⁻¹ (1 - s) =
      localEpsilon χ ψ s * localLFactor χ⁻¹ (1 - s) := by sorry
