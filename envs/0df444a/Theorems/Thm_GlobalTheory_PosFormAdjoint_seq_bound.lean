-- Prove2me | Theorems.Thm_GlobalTheory_PosFormAdjoint_seq_bound
-- name    : GlobalTheory.PosFormAdjoint.seq_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:51:11.069161+00:00
-- url     : https://prove2.me/theorems/d6fa6b33-188e-4549-a982-452104a6e2ff
-- title:
--   Pos Form Adjoint: seq bound
-- statement:
--   The Pos Form Adjoint construction uses the seq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosSemidefQuadraticAdjointPairBound.lean#L36-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PosSemidefQuadraticAdjointPairBound.lean#L36-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosSemidefQuadraticAdjointPairBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PosFormAdjoint

theorem GlobalTheory.PosFormAdjoint.seq_bound (a c : ℕ → ℤ) (n : ℕ) (hpos : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hrec : a n + ∑ i ∈ Finset.range n, c i * a i = 0) :
    a 1 ≤ (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) * a 0 := by sorry
