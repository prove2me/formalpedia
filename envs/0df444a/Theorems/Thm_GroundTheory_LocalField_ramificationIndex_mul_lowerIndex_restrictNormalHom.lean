-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_lowerIndex_restrictNormalHom
-- name    : GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_restrictNormalHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:34:03.775574+00:00
-- url     : https://prove2.me/theorems/491b642e-3ee8-5d66-8ba2-88841cf86af6
-- title:
--   Local Field: ramification Index mul lower Index restrict Normal Hom
-- statement:
--   The Local Field construction uses the ramification Index mul lower Index restrict Normal Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (M : IntermediateField K L)
variable [IsGalois K L]

theorem GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_restrictNormalHom [Normal K M] (σ : L ≃ₐ[K] L) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) := by sorry
