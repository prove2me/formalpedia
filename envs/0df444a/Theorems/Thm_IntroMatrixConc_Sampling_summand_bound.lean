-- Prove2me | Theorems.Thm_IntroMatrixConc_Sampling_summand_bound
-- name    : IntroMatrixConc.Sampling.summand_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:39.688915+00:00
-- url     : https://prove2.me/theorems/85f7bd35-2f29-413d-87d0-e7c90c67c2c7
-- title:
--   Proof of Corollary 6.2.1 — centered summand bound
-- statement:
--   Let $R_1,\ldots,R_n$ be independent copies of a measurable complex $d_1\times d_2$ random matrix $R$, where $n>0$ and $d_1,d_2\ge1$. Suppose $\mathbb ER=B$ and $\|R\|\le L$ almost surely. Define the centered, scaled summands $S_k=n^{-1}(R_k-B)$. Then $S_1,\ldots,S_n$ are independent and identically distributed, each has $\mathbb ES_k=0$, and for every $k$
--
--   $$
--   \|S_k\|\le\frac{2L}{n}\qquad\text{almost surely}.
--   $$
--
--   These are the hypotheses of the matrix Bernstein inequality that the proof of Corollary 6.2.1 checks for the estimator error $\overline R_n-B=\sum_k S_k$.
--
--   **Formalization Note** "Independent copy" is `iIndepFun` of the family together with equality in law (`IdentDistrib`) to a reference matrix $R_0$; the almost-sure bound is the page's $\|R\|\le L$. The statement includes the page's preceding sentence (i.i.d. family, mean zero) as well as the displayed norm bound.
-- source:
--   Tropp, arXiv:1501.01571v1, §6.2.2, proof of Corollary 6.2.1, p. 82 (PDF p. 88), summand-bound display

import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Sampling

/-- Tropp, proof of Corollary 6.2.1, p. 82 (PDF p. 88): the centered summands are i.i.d.,
have mean zero, and satisfy `‖S_k‖ ≤ 2L/n` almost surely. -/
theorem summand_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    let S := fun (k : Fin n) (ω : Ω) => ((n : ℝ)⁻¹) • (R k ω - B)
    iIndepFun S μ ∧ (∀ k j, IdentDistrib (S k) (S j) μ μ) ∧
    (∀ k, (∫ ω, S k ω ∂μ) = 0) ∧
    ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ 2 * L / n := by sorry

end IntroMatrixConc.Sampling
