-- Prove2me | Theorems.Thm_GlobalTheory_jacForm_mul
-- name    : GlobalTheory.jacForm_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:26.637457+00:00
-- url     : https://prove2.me/theorems/fdaa7c45-86b9-4562-aa8b-790c2ebea6d5
-- title:
--   Global Theory: jac Form mul
-- statement:
--   The Global Theory construction uses the jac Form mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L143-L146

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
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem GlobalTheory.jacForm_mul (h : A) (f : Fin (D + 1) → A) :
    jacForm d ω (fun i => h * f i) = h ^ (D + 1) • jacForm d ω f := by sorry
