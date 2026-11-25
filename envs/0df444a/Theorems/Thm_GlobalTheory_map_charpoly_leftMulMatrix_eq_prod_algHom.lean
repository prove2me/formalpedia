-- Prove2me | Theorems.Thm_GlobalTheory_map_charpoly_leftMulMatrix_eq_prod_algHom
-- name    : GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:59.065052+00:00
-- url     : https://prove2.me/theorems/ada424ba-e069-4693-b7b4-453d9d9e4e17
-- title:
--   Global Theory: map charpoly left Mul Matrix eq prod alg Hom
-- statement:
--   The Global Theory construction uses the map charpoly left Mul Matrix eq prod alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L104-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L104-L123

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

theorem GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    (Algebra.leftMulMatrix e x).charpoly.map (algebraMap R L) = ∏ j, (X - C (P j x)) := by sorry
