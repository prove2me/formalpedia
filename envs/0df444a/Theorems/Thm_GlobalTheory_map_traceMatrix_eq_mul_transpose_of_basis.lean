-- Prove2me | Theorems.Thm_GlobalTheory_map_traceMatrix_eq_mul_transpose_of_basis
-- name    : GlobalTheory.map_traceMatrix_eq_mul_transpose_of_basis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:08.716137+00:00
-- url     : https://prove2.me/theorems/db603484-99ea-4b6a-bf58-32df04e82ccc
-- title:
--   Global Theory: map trace Matrix eq mul transpose of basis
-- statement:
--   The Global Theory construction uses the map trace Matrix eq mul transpose of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L145-L150

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

theorem GlobalTheory.map_traceMatrix_eq_mul_transpose_of_basis {κ : Type*} (e : Basis ι R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : κ → S) :
    (Algebra.traceMatrix R v).map (algebraMap R L) =
      (Matrix.of fun i j => P j (v i)) * (Matrix.of fun i j => P j (v i)).transpose := by sorry
