-- Prove2me | Theorems.Thm_HighDimProb_QuadraticForms_bilinear_mgf_reduction
-- name    : HighDimProb.QuadraticForms.bilinear_mgf_reduction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-01T17:10:40.320805+00:00
-- url     : https://prove2.me/theorems/5399b195-a514-405f-b747-02d4cc5f695a
-- title:
--   Hanson–Wright: exponential-moment reduction of a decoupled bilinear form
-- statement:
--   Let $X:\Omega\to\mathbb R^n$ be a measurable random vector on a probability space $(\Omega,P)$. Let $Y:\Omega'\to\mathbb R^m$ have independent, centered, measurable coordinates on a probability space $(\Omega',Q)$. Assume that, for each $j$, there is an $s>0$ for which $\exp(Y_j^2/s^2)$ is integrable and $\mathbb E_Q\exp(Y_j^2/s^2)\le2$. Let $K>0$ bound all the Orlicz norms $\|Y_j\|_{\psi_2,Q}$ defined as the infimum of those admissible $s$.
--
--   For every real $n\times m$ matrix $A$ and every $u\in\mathbb R$, if
--   $$\exp\!\left(4u^2K^2\sum_j\left(\sum_i A_{ij}X_i\right)^2\right)$$
--   is integrable under $P$, then $\exp(uX^TAY)$ is integrable under the product measure $P\otimes Q$, and
--   $$\mathbb E_{P\otimes Q}\exp(uX^TAY)\le\mathbb E_P\exp\!\left(4u^2K^2\|A^TX\|_2^2\right).$$
--   The product measure makes $X$ and $Y$ independent. No independence, centering, or subgaussian assumption on $X$ is required for this reduction. Empty coordinate sets are allowed.
--
--   This supplies the exponential-moment conditioning step after decoupling in the Hanson–Wright proof. The remaining squared-norm moment can be estimated by Gaussian comparison to obtain the Frobenius/operator-norm dependence. The constant $4$ is explicit for the companion definition's exponential-square Orlicz norm; the proof does not assume that its defining infimum is attained.
-- source:
--   Rudelson–Vershynin, Hanson–Wright inequality and sub-gaussian concentration (2013), https://arxiv.org/pdf/1306.2872, p. 4, equation (1.4). Product-space version with the explicit constant 4 for the mission's Orlicz norm convention.

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.QuadraticForms

theorem bilinear_mgf_reduction {n m : ℕ} {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Fin n → Ω → ℝ) (Y : Fin m → Ω' → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y Q) (hmean : ∀ j, ∫ ω, Y j ω ∂Q = 0)
    (hsg : ∀ j, ∃ s > 0, Integrable (fun ω => exp (Y j ω ^ 2 / s ^ 2)) Q ∧
      ∫ ω, exp (Y j ω ^ 2 / s ^ 2) ∂Q ≤ 2)
    (A : Matrix (Fin n) (Fin m) ℝ) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ j, HighDimProb.Concentration.subgaussianNorm Q (Y j) ≤ K)
    (l : ℝ)
    (hbound : Integrable (fun ω =>
      exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2)) P) :
    Integrable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) (P.prod Q) ∧
    (∫ z : Ω × Ω', exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2) ∂P.prod Q) ≤
      ∫ ω, exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2) ∂P := by sorry

end HighDimProb.QuadraticForms
