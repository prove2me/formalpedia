-- Prove2me | Theorems.Thm_GlobalTheory_MultSieve_reduced_inj
-- name    : GlobalTheory.MultSieve.reduced_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:47.322967+00:00
-- url     : https://prove2.me/theorems/c7cda063-c5df-48de-8aab-fe6c79a18d4e
-- title:
--   Mult Sieve: reduced inj
-- statement:
--   The Mult Sieve construction uses the reduced inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L131-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.MultSieve

theorem GlobalTheory.MultSieve.reduced_inj {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by sorry
