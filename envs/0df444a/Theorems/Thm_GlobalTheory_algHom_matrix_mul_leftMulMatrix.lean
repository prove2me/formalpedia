-- Prove2me | Theorems.Thm_GlobalTheory_algHom_matrix_mul_leftMulMatrix
-- name    : GlobalTheory.algHom_matrix_mul_leftMulMatrix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:23.088917+00:00
-- url     : https://prove2.me/theorems/8eea0f71-7547-4696-bca4-476b5f04d730
-- title:
--   Global Theory: alg Hom matrix mul left Mul Matrix
-- statement:
--   The Global Theory construction uses the alg Hom matrix mul left Mul Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L94-L102

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
omit [IsDomain L]

theorem GlobalTheory.algHom_matrix_mul_leftMulMatrix (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by sorry
