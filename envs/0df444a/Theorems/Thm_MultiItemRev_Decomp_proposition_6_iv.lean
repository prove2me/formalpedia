-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_proposition_6_iv
-- name    : MultiItemRev.Decomp.proposition_6_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:30.74031+00:00
-- url     : https://prove2.me/theorems/9bcb834c-bfdd-47bd-96a0-71f154cc4499
-- title:
--   Proposition 6 (iv), p. 14 — E[s(X)1_{X∈A}] ≤ Rev(X1_{X∈A}) ≤ Rev(X)
-- statement:
--   Let $\mu = (q, s)$ be an IC and IR mechanism (with measurable $s$), let $X$ be a $k$-good random valuation in $\mathbb{R}^k_+$, $k \ge 1$, and let $A \subseteq \mathbb{R}^k_+$ be a measurable set of values of $X$. Then
--   $$
--   \mathbb{E}\big[s(X)\,\mathbf 1_{X \in A}\big] \le \mathrm{Rev}\big(X\,\mathbf 1_{X \in A}\big) \le \mathrm{Rev}(X).
--   $$
--
--   The revenue that any IC and IR mechanism collects on a subdomain of valuations cannot exceed the optimal revenue, even when the mechanism has positive transfers ($s < 0$ somewhere). This is how the marginal mechanisms of Theorem A and Lemma 8, whose payments may be negative, are bounded by $\mathrm{Rev}(Y)$.
--
--   **Formalization Note** The left side is $\int_A s^+\,d\mu - \int_A s^-\,d\mu$ in the extended reals, so it may be negative or $+\infty$; it is compared with $\mathrm{Rev}(X \mathbf 1_{X\in A})$ as an extended real and is not clipped. The set $A$ is assumed measurable ("a set of values of $X$"), so that $X \mathbf 1_{X \in A}$ is a random variable.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 14, Proposition 6 (iv)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem proposition_6_iv {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ≥0)) [IsProbabilityMeasure μ]
    (M : Mechanism ι) (hM : IsAdmissible M)
    (A : Set (ι → ℝ≥0)) (hA : MeasurableSet A) :
    ((∫⁻ x in A, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) -
        ((∫⁻ x in A, ENNReal.ofReal (-M.s x) ∂μ : ℝ≥0∞) : EReal) ≤ (Rev (lawOn μ A) : EReal) ∧
      Rev (lawOn μ A) ≤ Rev μ := by sorry

end MultiItemRev.Decomp
