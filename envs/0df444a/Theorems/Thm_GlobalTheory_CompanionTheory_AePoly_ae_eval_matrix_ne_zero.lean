-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_ae_eval_matrix_ne_zero
-- name    : GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:39.783681+00:00
-- url     : https://prove2.me/theorems/4b45d5c7-0cc2-4ed2-a45c-f6e9792989da
-- title:
--   Ae Poly: ae eval matrix ne zero
-- statement:
--   The Ae Poly construction uses the ae eval matrix ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L75-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L75-L94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AePoly

theorem GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 →
    ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by sorry
