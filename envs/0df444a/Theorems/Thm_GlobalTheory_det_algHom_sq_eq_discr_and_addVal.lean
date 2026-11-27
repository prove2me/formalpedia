-- Prove2me | Theorems.Thm_GlobalTheory_det_algHom_sq_eq_discr_and_addVal
-- name    : GlobalTheory.det_algHom_sq_eq_discr_and_addVal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:59.119309+00:00
-- url     : https://prove2.me/theorems/5a8bf639-f9bc-4e8f-a415-75ee57c789d7
-- title:
--   Global Theory: det alg Hom sq eq discr and add Val
-- statement:
--   The Global Theory construction uses the det alg Hom sq eq discr and add Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L340-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L340-L350

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
variable {R S L ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [Algebra R S] [CommRing L] [IsDomain L] [Algebra R L] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.det_algHom_sq_eq_discr_and_addVal (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (v : ι → S) :
    (Matrix.of fun i j => P j (v i)).det ^ 2 = algebraMap R L (Algebra.discr R v) ∧
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e ∧
    Algebra.discr R e ≠ 0 ∧
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) ∧
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) := by sorry
