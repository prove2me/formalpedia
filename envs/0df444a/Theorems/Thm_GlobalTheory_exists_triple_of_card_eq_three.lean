-- Prove2me | Theorems.Thm_GlobalTheory_exists_triple_of_card_eq_three
-- name    : GlobalTheory.exists_triple_of_card_eq_three
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:44.002603+00:00
-- url     : https://prove2.me/theorems/ac26b646-2596-4ece-b341-c9a1ea39426e
-- title:
--   Global Theory: exists triple of card eq three
-- statement:
--   The Global Theory construction uses the exists triple of card eq three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L28-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory

theorem GlobalTheory.exists_triple_of_card_eq_three {ι : Type*} [LinearOrder ι] {t : Finset ι}
    (ht : t.card = 3) : ∃ i j l, i < j ∧ j < l ∧ t = {i, j, l} := by sorry
