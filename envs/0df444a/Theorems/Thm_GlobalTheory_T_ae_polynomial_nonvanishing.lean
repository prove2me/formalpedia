-- Prove2me | Theorems.Thm_GlobalTheory_T_ae_polynomial_nonvanishing
-- name    : GlobalTheory.T.ae_polynomial_nonvanishing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:10.709921+00:00
-- url     : https://prove2.me/theorems/dbeb2f12-187c-5f4d-95e2-2f5eb9b1f773
-- title:
--   T: ae polynomial nonvanishing
-- statement:
--   The T construction uses the ae polynomial nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ae_polynomial_nonvanishing : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 → ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by sorry
