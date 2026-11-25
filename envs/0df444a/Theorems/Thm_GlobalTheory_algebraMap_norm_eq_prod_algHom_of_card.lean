-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_norm_eq_prod_algHom_of_card
-- name    : GlobalTheory.algebraMap_norm_eq_prod_algHom_of_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:29.455451+00:00
-- url     : https://prove2.me/theorems/0ca85f96-829a-4906-bb77-768729dce463
-- title:
--   Global Theory: algebra Map norm eq prod alg Hom of card
-- statement:
--   The Global Theory construction uses the algebra Map norm eq prod alg Hom of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L167-L173

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
omit [DecidableEq ι]

theorem GlobalTheory.algebraMap_norm_eq_prod_algHom_of_card (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.norm R x) = ∏ j, P j x := by sorry
