-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_lemma_B_1_eq_20
-- name    : HighDimCLT.Hyperrect.lemma_B_1_eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:03.668348+00:00
-- url     : https://prove2.me/theorems/d6c5e656-c591-458a-b310-2a52411bd083
-- title:
--   Lemma B.1 (20), p. 2325 — E[φ₁(ξ₁)φ₂(ξ₂)] ≤ E[φ₁(ξ₁)φ₂(ξ₁)] + E[φ₁(ξ₂)φ₂(ξ₂)] without independence
-- statement:
--   Let $\varphi_1, \varphi_2 : \mathbb R \to [0, \infty)$ be nondecreasing functions and let $\xi_1, \xi_2$ be real-valued random variables, not necessarily independent. Assume that $\varphi_1(\xi_1)\varphi_2(\xi_2)$, $\varphi_1(\xi_1)\varphi_2(\xi_1)$ and $\varphi_1(\xi_2)\varphi_2(\xi_2)$ have finite expectations. Then
--
--   $$\mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_2)] \le \mathrm E[\varphi_1(\xi_1)\varphi_2(\xi_1)] + \mathrm E[\varphi_1(\xi_2)\varphi_2(\xi_2)].$$
--
--   This is the last sentence of Lemma B.1 ("(20) holds without independence"), a variant of Chebyshev's association inequality; it is the form used in the proof of Lemma 5.1.
--
--   **Formalization Note** The random variables are measurable functions on a probability space; the three integrability hypotheses are the page's "all the expectations exist and are finite" for the expectations in (20).
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), pp. 2324–2325, App. B, Lemma B.1, display (20) and last sentence

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

theorem lemma_B_1_eq_20 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (hφ₁ : Monotone φ₁) (hφ₂ : Monotone φ₂)
    (hφ₁0 : ∀ x, 0 ≤ φ₁ x) (hφ₂0 : ∀ x, 0 ≤ φ₂ x)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁ : Measurable ξ₁) (hξ₂ : Measurable ξ₂)
    (hi₁₁ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω)) P)
    (hi₂₂ : Integrable (fun ω => φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω)) P)
    (hi₁₂ : Integrable (fun ω => φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω)) P) :
    ∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₂ ω) ∂P ≤
      (∫ ω, φ₁ (ξ₁ ω) * φ₂ (ξ₁ ω) ∂P) + ∫ ω, φ₁ (ξ₂ ω) * φ₂ (ξ₂ ω) ∂P := by sorry

end HighDimCLT.Hyperrect
