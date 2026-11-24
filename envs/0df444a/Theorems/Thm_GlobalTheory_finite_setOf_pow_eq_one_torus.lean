-- Prove2me | Theorems.Thm_GlobalTheory_finite_setOf_pow_eq_one_torus
-- name    : GlobalTheory.finite_setOf_pow_eq_one_torus
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:17.606876+00:00
-- url     : https://prove2.me/theorems/22ec2358-9366-4dbe-9251-e1ebf64e00fd
-- title:
--   Global Theory: finite set Of pow eq one torus
-- statement:
--   The Global Theory construction uses the finite set Of pow eq one torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L206-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L206-L215

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

theorem GlobalTheory.finite_setOf_pow_eq_one_torus [Module.Finite ℤ X] {m : ℕ} (hm : m ≠ 0) :
    {s : Multiplicative X →* Rˣ | s ^ m = 1}.Finite := by sorry
