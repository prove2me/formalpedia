-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_specMap_fractionField
-- name    : GlobalTheory.isOpenImmersion_specMap_fractionField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:07.38083+00:00
-- url     : https://prove2.me/theorems/534c3aa6-29bc-4b0b-ae31-6c47b1bf1dc4
-- title:
--   Global Theory: is Open Immersion spec Map fraction Field
-- statement:
--   The Global Theory construction uses the is Open Immersion spec Map fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L355-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L355-L369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem GlobalTheory.isOpenImmersion_specMap_fractionField :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by sorry
