-- Prove2me | Theorems.Thm_HighDimStat_Concentration_product_entropy_of_sq_decrements
-- name    : HighDimStat.Concentration.product_entropy_of_sq_decrements
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T21:05:42.902433+00:00
-- url     : https://prove2.me/theorems/40073c8c-2002-4014-a05a-976e55f61819
-- title:
--   Exponential entropy from bounded coordinate decrements on a product space
-- statement:
--   Let $P=\bigotimes_{i=1}^n P_i$ be a finite product of probability measures and let $Z$ be a measurable real function with $|Z|\le C$, where $C\ge0$. For each coordinate $i$, let $c_i$ be a measurable lower reference satisfying $c_i(x)\le Z(x)$ and remaining constant when only coordinate $i$ changes. If
--
--   $$\sum_{i=1}^n (Z(x)-c_i(x))^2\le V\qquad\text{for every }x,$$
--
--   where $V\ge0$, then for every $\lambda\ge0$,
--
--   $$H_P(e^{\lambda Z})\le\frac{\lambda^2V}{2}\,\mathbb E_P[e^{\lambda Z}].$$
--
--   Here $H_P(Y)=\mathbb E_P[Y\log Y]-\mathbb E_P[Y]\log\mathbb E_P[Y]$. Boundedness supplies all integrability needed for these expressions. This is a derived entropy-method lemma intended for Theorem 3.4, separately convex Lipschitz concentration. It combines product entropy tensorization with a constant-reference entropy bound and $e^{-u}-1+u\le u^2/2$ for $u\ge0$; it is not a verbatim theorem statement from the cited book.
-- source:
--   Derived entropy-method lemma: Wainwright, High-Dimensional Statistics (CUP, 2019), Section 3.1.4, printed pp. 64–67, Lemma 3.8 (entropy tensorization), together with the entropy variational principle in Eq. (3.24) and Exercise 3.9. The nonnegative decrement refinement uses the elementary inequality exp(-u)-1+u ≤ u²/2.

import Mathlib
import Definitions.Def_HighDimStat_Concentration_phiEntropy

open MeasureTheory ProbabilityTheory

namespace HighDimStat.Concentration

theorem product_entropy_of_sq_decrements {n : ℕ} {α : Fin n → Type}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (c : Fin n → (∀ i, α i) → ℝ)
    (hZ : Measurable Z) (hc : ∀ k, Measurable (c k))
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hZb : ∀ x, |Z x| ≤ C)
    (hclo : ∀ k x, c k x ≤ Z x)
    (hcfiber : ∀ k x t, c k (Function.update x k t) = c k x)
    (hsum : ∀ x, (∑ k, (Z x - c k x) ^ 2) ≤ V)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    phiEntropy (fun x => Real.exp (lam * Z x)) (Measure.pi μ) ≤
      lam ^ 2 / 2 * V * ∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ) := by sorry

end HighDimStat.Concentration
