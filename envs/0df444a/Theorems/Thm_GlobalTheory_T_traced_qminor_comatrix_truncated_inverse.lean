-- Prove2me | Theorems.Thm_GlobalTheory_T_traced_qminor_comatrix_truncated_inverse
-- name    : GlobalTheory.T.traced_qminor_comatrix_truncated_inverse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:35.974797+00:00
-- url     : https://prove2.me/theorems/7a8926ec-dd78-4cd6-8b50-519364cabcc8
-- title:
--   T: traced qminor comatrix truncated inverse
-- statement:
--   The T construction uses the traced qminor comatrix truncated inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TracedQminorComatrixTruncatedInverseStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TracedQminorComatrixTruncatedInverseStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TracedQminorComatrixTruncatedInverse
import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TracedQminorComatrixTruncatedInverseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.traced_qminor_comatrix_truncated_inverse : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by sorry
