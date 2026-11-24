-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_ae_eval_ne_zero_fin
-- name    : GlobalTheory.CompanionTheory.AePoly.ae_eval_ne_zero_fin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:16:43.605276+00:00
-- url     : https://prove2.me/theorems/e59d68b1-eb93-4183-b5dc-89eafc37284c
-- title:
--   Ae Poly: ae eval ne zero fin
-- statement:
--   The Ae Poly construction uses the ae eval ne zero fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L6-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AePolynomialNonvanishing.lean#L6-L58

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

theorem GlobalTheory.CompanionTheory.AePoly.ae_eval_ne_zero_fin : ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), MvPolynomial.eval x Q ≠ 0 := by sorry
