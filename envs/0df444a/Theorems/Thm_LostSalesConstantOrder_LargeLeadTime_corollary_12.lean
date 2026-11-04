-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_corollary_12
-- name    : LostSalesConstantOrder.LargeLeadTime.corollary_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:20.627984+00:00
-- url     : https://prove2.me/theorems/334636fb-010e-4272-9d82-8bc1e1323490
-- title:
--   Corollary 12 ($\mathbb E[D]$ restored): explicit bound on (7) for $L\ge8(\sigma^{-1}Q+1)m^{3/2}$
-- statement:
--   In the lost-sales system with demand law $\mathcal D$ (finite third moment, not deterministic), let $L\ge8(\sigma^{-1}Q+1)m^{3/2}$, let $\pi$ be an admissible policy that never orders more than $Q$ (such as $\bar\pi$ of Lemma 5), let $(\mathbf x^*,\mathcal I^*)$ solve problem (4), and $r^*=L^{-1}\sum_{i=1}^Lx^*_i$. Then for every $\tau\ge L+1$ the difference (7) satisfies
--   $$
--   \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi_{r^*}}_t\Big]-\mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^{\pi}_t\Big]\ \le\ 2^{12}h\big(Q+2^{3/2}\mathbb E[D]\big)\big(\mathbb E^2[D]+\mathbb E[D^2]\big)^3\sigma^{-6}m^3+c\,\mathbb E[D]\Big(\big\lceil(2ch^{-1}L)^{1/2}\big\rceil+2\Big).
--   $$
--
--   The first term does not depend on $L$ and the second grows like $\sqrt L$, so the per-window gap is $o(L)$: this is what makes the constant-order policy asymptotically optimal.
--
--   **Formalization Note** The paper prints the second term as $c(\lceil(2ch^{-1}L)^{1/2}\rceil+2)$, without the factor $\mathbb E[D]$. Its proof (p. 14) supposes $\mathcal I^*>(\lceil(2ch^{-1}L)^{1/2}\rceil+2)\mathbb E[D]$ and derives a contradiction, so it shows $\mathcal I^*\le(\lceil(2ch^{-1}L)^{1/2}\rceil+2)\mathbb E[D]$, and Theorem 8's term $c\mathcal I^*$ then gives the bound above. The printed bound is not invariant under rescaling the demand $D\mapsto\lambda D$ (every cost scales by $\lambda$, the printed second term does not), so the factor is a typographical slip. The difference is stated additively in $[0,\infty]$, the statement is for every policy that never orders more than $Q$, and the window starts at Lean period $t_0\ge L$, as in Theorem 8.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 14, Corollary 12 (E[D] restored in the second term, per its proof on p. 14)

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_ConstantOrder

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Corollary 12, p. 14, **with the factor `E[D]` of the second term restored**. If
`L ≥ 8(σ⁻¹Q + 1)m^{3/2}`, `π` is any admissible policy that a.s. never orders more than `Q`
(Lemma 5's `π̄` is one) and `(x*, 𝓘*)` any solution of (4), then for every window start `t₀ ≥ L`
(the paper's `τ ∈ [L + 1, T + 1]`) the difference (7) is at most
`2¹²h(Q + 2^{3/2}E[D])(E²[D] + E[D²])³σ⁻⁶m³ + c E[D](⌈(2ch⁻¹L)^{1/2}⌉ + 2)`.
The page prints `c(⌈(2ch⁻¹L)^{1/2}⌉ + 2)`; its proof shows `𝓘* ≤ (⌈(2ch⁻¹L)^{1/2}⌉ + 2)E[D]`. -/
theorem corollary_12 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (hL : 8 * ((Qlevel P prm : ℝ) / sigma P + 1) * (mConst P prm : ℝ) ^ ((3 : ℝ) / 2) ≤ prm.L)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I)
    (t₀ : ℕ) (ht₀ : prm.L ≤ t₀) :
    costWindow P prm (constantOrderPolicy P (rStar x)) t₀ ≤
      costWindow P prm π t₀ +
        ENNReal.ofReal
          (2 ^ 12 * prm.h * ((Qlevel P prm : ℝ) + 2 * Real.sqrt 2 * CappedBaseStock.mean P) *
              (CappedBaseStock.mean P ^ 2 + secondMoment P) ^ 3 / sigma P ^ 6 *
              (mConst P prm : ℝ) ^ 3 +
            prm.p * CappedBaseStock.mean P *
              ((⌈Real.sqrt (2 * prm.p / prm.h * prm.L)⌉₊ : ℝ) + 2)) := by sorry

end LostSalesConstantOrder.LargeLeadTime
