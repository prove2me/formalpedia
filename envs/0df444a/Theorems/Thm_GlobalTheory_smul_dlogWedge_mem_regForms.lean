-- Prove2me | Theorems.Thm_GlobalTheory_smul_dlogWedge_mem_regForms
-- name    : GlobalTheory.smul_dlogWedge_mem_regForms
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:48.970106+00:00
-- url     : https://prove2.me/theorems/d72509fd-ce56-48ad-80e4-806d41efc6d6
-- title:
--   Global Theory: smul dlog Wedge mem reg Forms
-- statement:
--   The Global Theory construction uses the smul dlog Wedge mem reg Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L184-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L184-L219

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

theorem GlobalTheory.smul_dlogWedge_mem_regForms (t : V) (ht : algebraMap V F t ≠ 0) (S : Finset (Fin p))
    (x : Fin p → F) (hS : ∀ k ∈ S, ∃ (m : ℤ) (u : Vˣ), x k = algebraMap V F u * algebraMap V F t ^ m)
    (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    t • dlogWedge K S x ∈ regForms K V F p := by sorry
