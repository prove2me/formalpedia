-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_lowerIndex_eq_sum_fiber
-- name    : GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_eq_sum_fiber
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:20.641135+00:00
-- url     : https://prove2.me/theorems/ab834914-7aba-4506-85f5-f84c88ec96ad
-- title:
--   Local Field: ramification Index mul lower Index eq sum fiber
-- statement:
--   The Local Field construction uses the ramification Index mul lower Index eq sum fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L62-L77

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
open Classical

theorem GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_eq_sum_fiber [Normal K M] (s : M ≃ₐ[K] M) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M s =
      ∑ σ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L ↦ AlgEquiv.restrictNormalHom M σ = s),
        lowerIndex K L σ := by sorry
