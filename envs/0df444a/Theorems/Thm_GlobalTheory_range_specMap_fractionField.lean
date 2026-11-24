-- Prove2me | Theorems.Thm_GlobalTheory_range_specMap_fractionField
-- name    : GlobalTheory.range_specMap_fractionField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:53.524749+00:00
-- url     : https://prove2.me/theorems/7cc0cf07-0788-4b79-890e-6851bd200b62
-- title:
--   Global Theory: range spec Map fraction Field
-- statement:
--   The Global Theory construction uses the range spec Map fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L340-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L340-L353

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

theorem GlobalTheory.range_specMap_fractionField :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
      {x : Spec (.of O) | x ≠ closedPoint O} := by sorry
