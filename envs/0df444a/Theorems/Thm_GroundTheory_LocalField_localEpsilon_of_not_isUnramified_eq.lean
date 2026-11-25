-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_not_isUnramified_eq
-- name    : GroundTheory.LocalField.localEpsilon_of_not_isUnramified_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:11.700804+00:00
-- url     : https://prove2.me/theorems/4548d85b-b030-5234-b69c-84cc861a5d90
-- title:
--   Local Field: local Epsilon of not is Unramified eq
-- statement:
--   The Local Field construction uses the local Epsilon of not is Unramified eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L330-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L330-L353

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

theorem GroundTheory.LocalField.localEpsilon_of_not_isUnramified_eq (hr : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      (residueCard K : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * s) *
        (((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
            valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
          quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K := by sorry
