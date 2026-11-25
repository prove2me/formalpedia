-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPolynomialEvaluation_main
-- name    : GlobalTheory.SmoothPolynomialEvaluation.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:52.477168+00:00
-- url     : https://prove2.me/theorems/ff3475d8-0232-5cac-a28f-f861360046e4
-- title:
--   Smooth Polynomial Evaluation: main
-- statement:
--   The Smooth Polynomial Evaluation construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L32-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L32-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SmoothPolynomialEvaluation

theorem GlobalTheory.SmoothPolynomialEvaluation.main : ∀ {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ) (a : ℂ),
    Polynomial.eval a (Polynomial.map (MvPolynomial.eval x₀) p) = (0 : ℂ) →
    Polynomial.eval a ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)
      (Polynomial.map (MvPolynomial.eval x₀) p)) ≠ (0 : ℂ) →
    ∃ (y : (Fin d → ℂ) → ℂ), y x₀ = a ∧ (∃ s ∈ nhds x₀, ContinuousOn y s) ∧
      ∀ᶠ (x : Fin d → ℂ) in nhds x₀,
        Polynomial.eval (y x) (Polynomial.map (MvPolynomial.eval x) p) = (0 : ℂ) := by sorry
