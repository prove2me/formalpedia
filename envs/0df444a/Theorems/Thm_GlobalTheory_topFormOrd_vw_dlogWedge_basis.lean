-- Prove2me | Theorems.Thm_GlobalTheory_topFormOrd_vw_dlogWedge_basis
-- name    : GlobalTheory.topFormOrd_vw_dlogWedge_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:50.922816+00:00
-- url     : https://prove2.me/theorems/daa1b0b7-3bee-54bc-be5c-5d19dddae89a
-- title:
--   Global Theory: top Form Ord vw dlog Wedge basis
-- statement:
--   The Global Theory construction uses the top Form Ord vw dlog Wedge basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L426-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L426-L431

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

theorem GlobalTheory.topFormOrd_vw_dlogWedge_basis (z : Fin n → V) (c : Basis (Fin n) V Ω[V⁄K])
    (hc : ∀ k, c k = D K V (z k)) {i : Fin n} (hi : Irreducible (z i)) :
    topFormOrd_vw F b (dlogWedge K {i} fun k => algebraMap V F (z k)) = ((-1 : ℤ) : WithTop ℤ) := by sorry
