-- Prove2me | Theorems.Thm_InfoInundation_Screening_eq_5
-- name    : InfoInundation.Screening.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:20.307198+00:00
-- url     : https://prove2.me/theorems/8802dda5-1806-4bde-b2fd-f757d5722a28
-- title:
--   (5), p. 10 — given Σ = σ, a post is N(µ, σ² + s²) to the consumer, with density ψ((Z − µ)², √(2(σ² + s²)))
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a truth $\theta\sim\mathcal N(\mu,s^2)$ (the consumer's belief, $s>0$) and an independent noise $\epsilon\sim\mathcal N(0,1)$, and fix an accuracy value $\sigma\in\mathbb R$. Then the post $Z=\theta+\sigma\epsilon$ has law
--   $$Z\sim\mathcal N(\mu,\sigma^2+s^2),$$
--   and for every $z\in\mathbb R$ the likelihood of (5) is the density of this law:
--   $$\psi\Big((z-\mu)^2,\sqrt{2(\sigma^2+s^2)}\Big)=\frac{1}{\sqrt{2\pi(\sigma^2+s^2)}}\exp\Big(-\frac{(z-\mu)^2}{2(\sigma^2+s^2)}\Big).$$
--
--   This is equation (5) of the paper: from the consumer's perspective the likelihood of a post given its accuracy is a normal density with variance $\sigma^2+s^2$. It justifies the likelihood used in the posterior (4).
--
--   **Formalization Note.** Mathlib's `gaussianReal m v` and `gaussianPDFReal m v` take the **variance** $v$ as a nonnegative real, here $(\sigma^2+s^2)$ and $s^2$ cast with `toNNReal` (both nonnegative). The statement holds for every real $\sigma$, including $\sigma=0$; the paper only uses $\sigma$ in the support of $\mathbb G$.
-- source:
--   Allon, Drakopoulos & Manshadi, Information Inundation on Platforms and Implications, SSRN 3385627 (version of 2020-04-05), p. 10, proof of Proposition 1, eq. (5)

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model
open MeasureTheory ProbabilityTheory

namespace InfoInundation.Screening

theorem eq_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ s : ℝ) (hs : 0 < s) (θ ε : Ω → ℝ) (hθ : Measurable θ) (hε : Measurable ε)
    (hθlaw : P.map θ = gaussianReal μ (s ^ 2).toNNReal)
    (hεlaw : P.map ε = gaussianReal 0 1) (hind : IndepFun θ ε P) (σ : ℝ) :
    P.map (fun ω => θ ω + σ * ε ω) = gaussianReal μ (σ ^ 2 + s ^ 2).toNNReal ∧
      ∀ z : ℝ, likelihood μ s σ z = gaussianPDFReal μ (σ ^ 2 + s ^ 2).toNNReal z := by sorry

end InfoInundation.Screening
