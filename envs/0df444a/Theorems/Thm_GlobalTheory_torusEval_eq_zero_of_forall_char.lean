-- Prove2me | Theorems.Thm_GlobalTheory_torusEval_eq_zero_of_forall_char
-- name    : GlobalTheory.torusEval_eq_zero_of_forall_char
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:49.678363+00:00
-- url     : https://prove2.me/theorems/bf4e5079-5a62-43d4-9212-2de29ab83c34
-- title:
--   Global Theory: torus Eval eq zero of forall char
-- statement:
--   The Global Theory construction uses the torus Eval eq zero of forall char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L184-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L184-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]

theorem GlobalTheory.torusEval_eq_zero_of_forall_char (H : Subgroup (Multiplicative X →* Rˣ))
    {f : AddMonoidAlgebra R X} (hf : ∀ s ∈ H, torusEval s f = 0) {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : torusEval t f = 0 := by sorry
