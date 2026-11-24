-- Prove2me | Theorems.Thm_GlobalTheory_laurentEval_single
-- name    : GlobalTheory.laurentEval_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:58.521805+00:00
-- url     : https://prove2.me/theorems/7fa6c2c1-347a-4be6-a6c1-bc42a583f192
-- title:
--   Global Theory: laurent Eval single
-- statement:
--   The Global Theory construction uses the laurent Eval single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L338-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L338-L341

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
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] {ι : Type*}

theorem GlobalTheory.laurentEval_single (u : ι → Rˣ) (x : ι →₀ ℤ) (a : R) :
    laurentEval u (single x a) = a * ((x.prod fun i m => u i ^ m : Rˣ) : R) := by sorry
