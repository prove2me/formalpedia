-- Prove2me | Theorems.Thm_OnsagerReciprocal_integrable_norm_pow_mul_fluctuationWeight
-- name    : OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-10T23:34:25.179319+00:00
-- url     : https://prove2.me/theorems/7c01a050-1f02-4ed8-bad1-717e4f9f87cb
-- title:
--   Polynomial moments of the Gaussian fluctuation weight $e^{-\frac12 x^{\mathsf T}\beta x}$ are finite for positive definite $\beta$
-- statement:
--   Let $\beta$ be a positive definite symmetric real $n\times n$ matrix and let
--   $$w(x)=e^{-\frac12\beta_{ik}x_ix_k}=e^{-\frac12x^{\mathsf T}\beta x},\qquad x\in\mathbb R^n,$$
--   be the (unnormalized) Gaussian fluctuation weight. Then for every $m\in\mathbb N$ the function $x\mapsto\|x\|^m\,w(x)$ is Lebesgue integrable on $\mathbb R^n$:
--   $$\int_{\mathbb R^n}\|x\|^m\,e^{-\frac12x^{\mathsf T}\beta x}\,dx<\infty .$$
--
--   This is the analytic input behind every average $\langle f\rangle=\int f\,w\,dx/\int w\,dx$ of a polynomial in the fluctuations: it makes the normalization $\int w\,dx$ finite ($m=0$) and the first and second moments $\langle x_i\rangle$, $\langle x_ix_k\rangle$, $\langle X_ix_k\rangle$ well defined, which the source uses without comment. It is reusable for any computation with the multivariate Gaussian distribution of thermodynamic fluctuations.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` with Lebesgue measure and its sup norm $\|x\|=\max_i|x_i|$; since all norms on $\mathbb R^n$ are equivalent, the choice of norm does not affect the statement. Positive definiteness is `Matrix.PosDef`, which includes symmetry.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" (the Gaussian distribution w = Ã exp(-½ β_ik x_i x_k) and the averages over it used in the "Proof" subsection), following Landau–Lifshitz, Statistical Physics, Part 1; integrability of polynomial moments is listed as required analytic input in the mission description

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic

open Matrix

namespace OnsagerReciprocal
/-- Finiteness of the polynomial moments of the Gaussian fluctuation weight: for a positive
definite `β`, every function `x ↦ ‖x‖ ^ m * exp (-½ xᵀ β x)` is Lebesgue integrable on `ℝⁿ`. -/
theorem integrable_norm_pow_mul_fluctuationWeight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (m : ℕ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => ‖x‖ ^ m * fluctuationWeight β x) := by sorry
end OnsagerReciprocal
