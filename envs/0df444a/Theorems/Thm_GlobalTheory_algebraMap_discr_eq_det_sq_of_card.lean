-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_card
-- name    : GlobalTheory.algebraMap_discr_eq_det_sq_of_card
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:00.420828+00:00
-- url     : https://prove2.me/theorems/5304ce3b-7cc2-4e83-935c-f8e0ead6df86
-- title:
--   Global Theory: algebra Map discr eq det sq of card
-- statement:
--   The Global Theory construction uses the algebra Map discr eq det sq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L185-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
variable [Module.Free R S] [Module.Finite R S]

theorem GlobalTheory.algebraMap_discr_eq_det_sq_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by sorry
