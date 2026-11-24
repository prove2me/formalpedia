-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFinite_sum_sq_lt
-- name    : GlobalTheory.LaurentFinite.sum_sq_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:11.47175+00:00
-- url     : https://prove2.me/theorems/9ff88821-b2ca-4e9a-aeff-b9f5aeee588e
-- title:
--   Laurent Finite: sum sq lt
-- statement:
--   The Laurent Finite construction uses the sum sq lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L46-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L46-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra

theorem GlobalTheory.LaurentFinite.sum_sq_lt {m : ℕ} (j : ℤ) (ν κ : Fin m → ℤ) (hj : 2 ≤ j) (hν : ∀ i, |ν i| ≠ j - 1)
    (hκ : ∀ i, |κ i| ≤ 1) (hs : ∑ i, |κ i| ≤ ∑ i, |cut j (ν i)|)
    (hne : κ ≠ fun i => cut j (ν i)) :
    ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 < ∑ i, ν i ^ 2 := by sorry
