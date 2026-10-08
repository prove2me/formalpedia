-- Prove2me | Theorems.Thm_InfoGen_Expected_lemma_1
-- name    : InfoGen.Expected.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:16.48222+00:00
-- url     : https://prove2.me/theorems/7c752091-a2f1-454b-b453-55c22c89a711
-- title:
--   Lemma 1, p. 3 — if f(X̄,Ȳ) is σ-subgaussian under P_X ⊗ P_Y, then |E f(X,Y) − E f(X̄,Ȳ)| ≤ √(2σ² I(X;Y))
-- statement:
--   This is the decoupling estimate of Xu and Raginsky.
--
--   Let $(X,Y)$ be a pair of random variables on $\mathsf X\times\mathsf Y$ with joint law $P_{X,Y}$, and let $(\bar X,\bar Y)$ have law $P_{\bar X,\bar Y}=P_X\otimes P_Y$, so that $\bar X$ is an independent copy of $X$ and $\bar Y$ an independent copy of $Y$. Let $f:\mathsf X\times\mathsf Y\to\mathbb R$ and $\sigma\ge 0$. Suppose $f(\bar X,\bar Y)$ is $\sigma$-subgaussian under $P_X\otimes P_Y$, that is,
--   $$
--   \log\mathbb E\Big[e^{\lambda\,(f(\bar X,\bar Y)-\mathbb E f(\bar X,\bar Y))}\Big]\le\frac{\lambda^2\sigma^2}{2}\qquad\text{for all }\lambda\in\mathbb R,
--   $$
--   and that the mutual information $I(X;Y)=D(P_{X,Y}\|P_X\otimes P_Y)$ is finite. Then
--   $$
--   \big|\mathbb E[f(X,Y)]-\mathbb E[f(\bar X,\bar Y)]\big|\le\sqrt{2\sigma^2 I(X;Y)}.
--   $$
--
--   The lemma bounds how much the expectation of a function can change when a dependent pair is replaced by an independent one, in terms of the information shared by the two coordinates. Theorem 1 is the special case $X=S$, $Y=W$, $f(s,w)$ the (centred) empirical risk.
--
--   **Formalization Note** "σ-subgaussian" is Mathlib's `HasSubgaussianMGF` of the centred variable $f-\mathbb E_{P_X\otimes P_Y}f$ with variance proxy $\sigma^2$ (Mathlib's parameter is the square of the paper's $\sigma$); it includes integrability of every $e^{\lambda f}$ under the product. The hypothesis $I(X;Y)\neq\infty$ is added: on the page an infinite $I$ makes the bound vacuous, while in Lean $\infty$ would be read as $0$ by the conversion to a real number. No integrability of $f$ under $P_{X,Y}$ is assumed; it follows from the hypotheses.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Lemma 1, eq. (8), p. 3, with footnote 2 (p. 3); proof App. A, p. 11

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

/-- Lemma 1 (Xu & Raginsky, arXiv:1705.07809v2, p. 3, eq. (8); proof App. A, p. 11). Let `P` be
the joint law of `(X, Y)` and `P_X ⊗ P_Y` the law of independent copies `(X̄, Ȳ)`. If `f(X̄, Ȳ)` is
`σ`-subgaussian under `P_X ⊗ P_Y` (footnote 2: the centred variable has MGF at most
`exp(λ²σ²/2)`; Mathlib's variance proxy is `σ²`) and `I(X; Y) < ∞`, then
`|E f(X, Y) − E f(X̄, Ȳ)| ≤ √(2σ² I(X; Y))`. -/
theorem lemma_1 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure (α × β)) [IsProbabilityMeasure P] (f : α × β → ℝ) (σ : ℝ≥0)
    (hsub : HasSubgaussianMGF (fun q => f q - ∫ q', f q' ∂(P.fst.prod P.snd)) (σ ^ 2)
      (P.fst.prod P.snd))
    (hI : mutualInfo P ≠ ⊤) :
    |∫ q, f q ∂P - ∫ q, f q ∂(P.fst.prod P.snd)|
      ≤ Real.sqrt (2 * (σ : ℝ) ^ 2 * (mutualInfo P).toReal) := by sorry

end InfoGen.Expected
