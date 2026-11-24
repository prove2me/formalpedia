-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFinite_exists_gap
-- name    : GlobalTheory.LaurentFinite.exists_gap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:04.008804+00:00
-- url     : https://prove2.me/theorems/3f1927cf-6341-41d5-955e-7e2b98c5e36a
-- title:
--   Laurent Finite: exists gap
-- statement:
--   The Laurent Finite construction uses the exists gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicators.lean#L64-L76

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

theorem GlobalTheory.LaurentFinite.exists_gap {m : ℕ} (ν : Fin m → ℤ) (i0 : Fin m) (h : (m : ℤ) < |ν i0|) :
    ∃ j : ℤ, 2 ≤ j ∧ j ≤ |ν i0| ∧ ∀ i, |ν i| ≠ j - 1 := by sorry
