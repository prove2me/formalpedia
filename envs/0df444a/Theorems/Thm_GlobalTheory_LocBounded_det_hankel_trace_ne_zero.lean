-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_det_hankel_trace_ne_zero
-- name    : GlobalTheory.LocBounded.det_hankel_trace_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:23.996272+00:00
-- url     : https://prove2.me/theorems/ebe79415-9392-405c-9ee4-114a7051731c
-- title:
--   Loc Bounded: det hankel trace ne zero
-- statement:
--   The Loc Bounded construction uses the det hankel trace ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L73-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L73-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded

theorem GlobalTheory.LocBounded.det_hankel_trace_ne_zero (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K)
    (h : N.charpoly.Separable) :
    (Matrix.of fun j k : Fin n => (N ^ ((j : ℕ) + (k : ℕ))).trace).det ≠ 0 := by sorry
