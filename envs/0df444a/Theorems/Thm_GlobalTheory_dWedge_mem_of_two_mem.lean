-- Prove2me | Theorems.Thm_GlobalTheory_dWedge_mem_of_two_mem
-- name    : GlobalTheory.dWedge_mem_of_two_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:43.133402+00:00
-- url     : https://prove2.me/theorems/e2ddc55a-fb5e-4e7a-8c57-9e3fccfffe00
-- title:
--   Global Theory: d Wedge mem of two mem
-- statement:
--   The Global Theory construction uses the d Wedge mem of two mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L63-L91

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
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {p : ℕ}

theorem GlobalTheory.dWedge_mem_of_two_mem (t : A) (x : Fin p → A) {i j : Fin p} (hij : i ≠ j)
    (hi : t ∣ x i) (hj : t ∣ x j) :
    ∃ η : ⋀[A]^p Ω[A⁄R], dWedge R x = t • η := by sorry
