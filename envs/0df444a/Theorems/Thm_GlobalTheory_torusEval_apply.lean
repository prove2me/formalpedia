-- Prove2me | Theorems.Thm_GlobalTheory_torusEval_apply
-- name    : GlobalTheory.torusEval_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:01.480801+00:00
-- url     : https://prove2.me/theorems/09321580-508b-4417-aa1d-d0f10de32f31
-- title:
--   Global Theory: torus Eval apply
-- statement:
--   The Global Theory construction uses the torus Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L120-L122

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

theorem GlobalTheory.torusEval_apply (t : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra R X) :
    torusEval t f = f.coeff.sum fun x a => a * t (Multiplicative.ofAdd x) := by sorry
