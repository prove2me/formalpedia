-- Prove2me | Theorems.Thm_GlobalTheory_neg_one_le_topFormOrd_vw_dlogWedge
-- name    : GlobalTheory.neg_one_le_topFormOrd_vw_dlogWedge
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:31.116368+00:00
-- url     : https://prove2.me/theorems/c0c037db-cd2f-4a86-ae39-25a8317746f1
-- title:
--   Global Theory: neg one le top Form Ord vw dlog Wedge
-- statement:
--   The Global Theory construction uses the neg one le top Form Ord vw dlog Wedge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L407-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L407-L414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])

theorem GlobalTheory.neg_one_le_topFormOrd_vw_dlogWedge (S : Finset (Fin n)) (x : Fin n → F)
    (hS : ∀ k ∈ S, x k ≠ 0) (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (dlogWedge K S x) := by sorry
