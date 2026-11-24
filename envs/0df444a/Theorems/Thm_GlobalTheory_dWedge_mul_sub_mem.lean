-- Prove2me | Theorems.Thm_GlobalTheory_dWedge_mul_sub_mem
-- name    : GlobalTheory.dWedge_mul_sub_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:20.816645+00:00
-- url     : https://prove2.me/theorems/62337895-5346-4a77-b7da-4a098082967f
-- title:
--   Global Theory: d Wedge mul sub mem
-- statement:
--   The Global Theory construction uses the d Wedge mul sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L225-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential

theorem GlobalTheory.dWedge_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) := by sorry
