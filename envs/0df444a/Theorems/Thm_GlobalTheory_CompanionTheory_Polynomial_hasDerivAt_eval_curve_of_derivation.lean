-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Polynomial_hasDerivAt_eval_curve_of_derivation
-- name    : GlobalTheory.CompanionTheory.Polynomial.hasDerivAt_eval_curve_of_derivation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:43.480854+00:00
-- url     : https://prove2.me/theorems/146802b2-c072-4e39-83ce-1022a7a8a30c
-- title:
--   Polynomial: has Deriv At eval curve of derivation
-- statement:
--   The Polynomial construction uses the has Deriv At eval curve of derivation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtEvalCurveOfDerivation.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtEvalCurveOfDerivation.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtEvalCurveOfDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Polynomial

theorem GlobalTheory.CompanionTheory.Polynomial.hasDerivAt_eval_curve_of_derivation {σ : Type}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s)
    (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by sorry
