-- Prove2me | Theorems.Thm_MDPFinance_ConsumptionInvestment_regime_monotone_fraction
-- name    : MDPFinance.ConsumptionInvestment.regime_monotone_fraction
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:57.610014+00:00
-- url     : https://prove2.me/theorems/e15a103d-907c-4789-8d79-dd44168ee706
-- title:
--   Theorem 4.4.4 — $\le_{icv}$-monotone optimal fraction across regimes
-- statement:
--   One stock, support of $R(j)$ independent of $j$, common admissible fractions $\tilde A$;
--   $v(j) := \sup_{\alpha\in\tilde A}\mathbb{E}[(1+\alpha R(j))^\gamma]$ (Eq. 4.21) with optimal
--   $\alpha^*(j)$. If $Q_j \le_{\mathrm{icv}} Q_k$ then $\alpha^*(j) \le \alpha^*(k)$.
--
--   **Formalization Note (moderation).** The setting is the book's: power utility with
--   $0<\gamma<1$ (for $\gamma<0$ the problem is a minimization), the common admissible set
--   $\tilde A$ of fractions determined by the regime-independent support, and Assumption (FM) with
--   non-redundancy in each regime, which makes the optimal solutions $\alpha^*(j)$, $\alpha^*(k)$
--   unique (Remark 4.1.3); for an arbitrary set $\tilde A$ and possibly non-unique maximizers the
--   inequality can fail for a bad selection.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 104, PDF 118, Theorem 4.4.4

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_StochasticOrders

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.4.4 (Bäuerle–Rieder, p. 104, PDF 118). One stock, power utility with `0 < γ < 1`,
regime return laws `Q_j`, `Q_k` satisfying Assumption (FM) (no arbitrage, finite mean) and
non-redundant (the return is not a.s. `0`, so that the maximizer of (4.21) is unique, Remark
4.1.3), with the support of `R(·)` independent of the regime, so that the admissible fractions
form a common set `Ã := {α | 1 + α R(j) ≥ 0 a.s.} = {α | 1 + α R(k) ≥ 0 a.s.}`;
`v(·) := sup_{α ∈ Ã} 𝔼[(1+αR(·))^γ]` (Eq. (4.21)) with optimal solutions `α^*(j)`, `α^*(k)`. If
`Q_j ≤_icv Q_k` then `α^*(j) ≤ α^*(k)`: the fraction invested in the stock is larger in the
environment state with the increasing-concave-larger return distribution. -/
theorem regime_monotone_fraction (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Qj Qk : Measure ℝ) [IsProbabilityMeasure Qj] [IsProbabilityMeasure Qk]
    (hNAj : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qj, 0 ≤ a * y) ∧ Qj {y | 0 < a * y} > 0)
    (hNAk : ¬ ∃ a : ℝ, (∀ᵐ y ∂Qk, 0 ≤ a * y) ∧ Qk {y | 0 < a * y} > 0)
    (hintj : Integrable id Qj) (hintk : Integrable id Qk)
    (hnrj : Qj {y | y ≠ 0} ≠ 0) (hnrk : Qk {y | y ≠ 0} ≠ 0)
    (Atilde : Set ℝ) (hAj : Atilde = {α | ∀ᵐ y ∂Qj, 0 ≤ 1 + α * y})
    (hAk : Atilde = {α | ∀ᵐ y ∂Qk, 0 ≤ 1 + α * y})
    (hicv : LEIncreasingConcaveOrder Qj Qk)
    (αj αk : ℝ) (hαj_mem : αj ∈ Atilde)
    (hαj_opt : ∀ α ∈ Atilde, ∫ y, (1 + α * y) ^ γ ∂Qj ≤ ∫ y, (1 + αj * y) ^ γ ∂Qj)
    (hαk_mem : αk ∈ Atilde)
    (hαk_opt : ∀ α ∈ Atilde, ∫ y, (1 + α * y) ^ γ ∂Qk ≤ ∫ y, (1 + αk * y) ^ γ ∂Qk) :
    αj ≤ αk := by sorry

end MDPFinance.ConsumptionInvestment
