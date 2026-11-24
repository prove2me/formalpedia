-- Prove2me | Theorems.Thm_GlobalTheory_dlogWedge_mem_regForms
-- name    : GlobalTheory.dlogWedge_mem_regForms
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:02.139228+00:00
-- url     : https://prove2.me/theorems/c6718f62-95b4-45ad-9eb0-88795a757801
-- title:
--   Global Theory: dlog Wedge mem reg Forms
-- statement:
--   The Global Theory construction uses the dlog Wedge mem reg Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L174-L182

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
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]

theorem GlobalTheory.dlogWedge_mem_regForms (S : Finset (Fin p)) (x : Fin p → V)
    (hS : ∀ k ∈ S, IsUnit (x k)) :
    dlogWedge K S (fun k => algebraMap V F (x k)) ∈ regForms K V F p := by sorry
