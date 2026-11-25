-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_not_isUnramified
-- name    : GroundTheory.LocalField.localEpsilon_of_not_isUnramified
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:35.869735+00:00
-- url     : https://prove2.me/theorems/d498b1d8-1c3e-5dd2-86c3-51ede60ab887
-- title:
--   Local Field: local Epsilon of not is Unramified
-- statement:
--   The Local Field construction uses the local Epsilon of not is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L121-L126

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
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem GroundTheory.LocalField.localEpsilon_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
          valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
        quasiCharExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-s) * (ψ x : ℂ) ∂selfDualMeasure ψ := by sorry
