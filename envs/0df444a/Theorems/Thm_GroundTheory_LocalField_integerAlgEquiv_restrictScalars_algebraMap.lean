-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integerAlgEquiv_restrictScalars_algebraMap
-- name    : GroundTheory.LocalField.integerAlgEquiv_restrictScalars_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:49.720903+00:00
-- url     : https://prove2.me/theorems/ddc1b784-9746-5233-962f-6f5e56f51347
-- title:
--   Local Field: integer Alg Equiv restrict Scalars algebra Map
-- statement:
--   The Local Field construction uses the integer Alg Equiv restrict Scalars algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndexQuotient.lean#L47-L51

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

theorem GroundTheory.LocalField.integerAlgEquiv_restrictScalars_algebraMap (τ : L ≃ₐ[M] L) (y : 𝒪[M]) :
    integerAlgEquiv K L (τ.restrictScalars K) (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y := by sorry
