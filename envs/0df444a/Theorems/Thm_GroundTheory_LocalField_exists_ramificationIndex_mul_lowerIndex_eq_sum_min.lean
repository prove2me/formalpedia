-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_ramificationIndex_mul_lowerIndex_eq_sum_min
-- name    : GroundTheory.LocalField.exists_ramificationIndex_mul_lowerIndex_eq_sum_min
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:56.133745+00:00
-- url     : https://prove2.me/theorems/106276ad-621e-5c0b-8322-7d55e2927e39
-- title:
--   Local Field: exists ramification Index mul lower Index eq sum min
-- statement:
--   The Local Field construction uses the exists ramification Index mul lower Index eq sum min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L101-L112

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

theorem GroundTheory.LocalField.exists_ramificationIndex_mul_lowerIndex_eq_sum_min [Normal K M] (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
        ∑ τ : L ≃ₐ[M] L, min (lowerIndex M L τ) (lowerIndex K L σ₀) := by sorry
