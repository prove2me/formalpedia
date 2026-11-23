-- Prove2me | Theorems.Thm_GlobalTheory_MultSieve_farey_spaced
-- name    : GlobalTheory.MultSieve.farey_spaced
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:53.258446+00:00
-- url     : https://prove2.me/theorems/04fdd14e-61f3-45f2-9340-3c571d9c35df
-- title:
--   Mult Sieve: farey spaced
-- statement:
--   The Mult Sieve construction uses the farey spaced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L98-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L98-L129

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

theorem GlobalTheory.MultSieve.farey_spaced (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by sorry
