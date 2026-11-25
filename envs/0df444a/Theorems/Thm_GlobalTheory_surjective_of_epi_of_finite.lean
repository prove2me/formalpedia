-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_epi_of_finite
-- name    : GlobalTheory.surjective_of_epi_of_finite
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:02.430991+00:00
-- url     : https://prove2.me/theorems/0a2c6013-6153-54ff-ae41-efb407bcdcd9
-- title:
--   Global Theory: surjective of epi of finite
-- statement:
--   The Global Theory construction uses the surjective of epi of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsCounitEqOneMulEqZeroOfIsNilpotent.lean#L446-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsCounitEqOneMulEqZeroOfIsNilpotent.lean#L446-L448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Coalgebra Bialgebra HopfAlgebra WithConv
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [CategoryTheory.Epi f]
    (hf : f.hom.Finite) : Function.Surjective f := by sorry
