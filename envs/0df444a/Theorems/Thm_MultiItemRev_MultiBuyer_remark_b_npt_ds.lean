-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_remark_b_npt_ds
-- name    : MultiItemRev.MultiBuyer.remark_b_npt_ds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:12.79398+00:00
-- url     : https://prove2.me/theorems/3149e3e9-7838-462c-aab7-9ae817c6bea7
-- title:
--   Remark (b) of A.7, p. 48 — DS case: NPT ⇔ sʲ(0, x⁻ʲ) = 0, and NPT is without loss of generality for Rev^DS
-- statement:
--   Let $n \ge 1$ buyers and $k \ge 1$ goods be given, and let $X$ be a random valuation profile in $\mathbb R^{kn}_+$ with law $\mu$.
--
--   1. A feasible, IC-DS and IR-DS mechanism $(q^j, s^j)_{j}$ with measurable payments satisfies NPT ($s^j \ge 0$ everywhere) if and only if
--   $$s^j(0, x^{-j}) = 0 \quad \text{for every buyer } j \text{ and every } x^{-j}.$$
--   2. The optimal dominant-strategy revenue is attained by NPT mechanisms:
--   $$\mathrm{Rev}^{DS}(X) = \sup\{R(\mu; X) : \mu \text{ feasible, IC-DS, IR-DS, NPT, with measurable payments}\}.$$
--
--   This is the multi-buyer version of Proposition 6 (i)–(iii) of the paper; the proof of Theorem 33 starts from an NPT mechanism, which this result justifies.
--
--   **Formalization Note** $(0, x^{-j})$ is `Function.update x j 0`. The hypotheses $n \ge 1$ and $k \ge 1$ (`[Nonempty ι]`) are those of the Remark.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 48, Appendix A.7, Remark (b), dominant strategy case

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- Remark (b) of Appendix A.7, dominant strategy case (p. 48): for an IC-DS and IR-DS mechanism,
NPT is equivalent to `s^j(0, x^{-j}) = 0` for all `j` and `x^{-j}`; and NPT can be assumed without
loss of generality when maximizing revenue. -/
theorem remark_b_npt_ds {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (Fin n → ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    (∀ M : MechanismN n ι, IsAdmissibleDS M →
      (IsNPTN M ↔ ∀ (x : Fin n → ι → ℝ≥0) (j : Fin n), M.s (Function.update x j 0) j = 0)) ∧
    RevDS μ = ⨆ (M : MechanismN n ι) (_ : IsAdmissibleDS M ∧ IsNPTN M),
      (expRevenueN μ M).toENNReal := by sorry

end MultiItemRev.MultiBuyer
