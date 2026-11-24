-- Prove2me | Theorems.Thm_GlobalTheory_residueField_map_adicCompletion_surjective
-- name    : GlobalTheory.residueField_map_adicCompletion_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:08.732662+00:00
-- url     : https://prove2.me/theorems/f2305a43-81c8-44e2-a0ff-93c3ff8a1191
-- title:
--   Global Theory: residue Field map adic Completion surjective
-- statement:
--   The Global Theory construction uses the residue Field map adic Completion surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueFieldMapAdicCompletionSurjective.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueFieldMapAdicCompletionSurjective.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueFieldMapAdicCompletionSurjective
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

theorem GlobalTheory.residueField_map_adicCompletion_surjective (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by sorry
