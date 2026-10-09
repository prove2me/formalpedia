-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_subdomain_ds
-- name    : MultiItemRev.MultiBuyer.subdomain_ds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:20.069105+00:00
-- url     : https://prove2.me/theorems/3a23eb0b-ca21-4aad-a689-960999105302
-- title:
--   Remark (b) of A.7, p. 48 — DS subdomain property: E[Σⱼ sʲ(X) 1_{X∈A}] ≤ Rev^DS(X 1_{X∈A}) ≤ Rev^DS(X)
-- statement:
--   Let $n \ge 1$ buyers and $k \ge 1$ goods be given, let $X$ be a random valuation profile in $\mathbb R^{kn}_+$, let $\mu = (q^j, s^j)_j$ be a feasible, IC-DS and IR-DS mechanism with measurable payments and seller revenue $S = \sum_j s^j$, and let $A \subseteq \mathbb R^{kn}_+$ be a measurable set. Assume the signed expectation of $S(X)\mathbf 1_{X\in A}$ is defined: at least one of its positive and negative part integrals is finite. Then
--   $$\mathbb E\Big[\sum_j s^j(X)\,\mathbf 1_{X\in A}\Big] \le \mathrm{Rev}^{DS}(X\,\mathbf 1_{X\in A}) \le \mathrm{Rev}^{DS}(X),$$
--   where $X\mathbf 1_{X\in A}$ equals $X$ on $\{X\in A\}$ and $0$ otherwise. The mechanism $\mu$ need not satisfy NPT.
--
--   This is the multi-buyer version of Proposition 6 (iv): the revenue that a mechanism collects on a subdomain of valuations never exceeds the optimal revenue. It is the step of the proof of Theorem 33 that bounds the revenue of the marginal mechanism.
--
--   **Formalization Note** The left side is $\int_A S^+\,d\mu - \int_A S^-\,d\mu$ in `EReal`. The definedness condition excludes $+\infty-\infty$, for which the paper's expectation has no value. The law of $X\mathbf 1_{X\in A}$ is `lawOnN μ A`, the image of $\mu$ under the indicator map, which is why $A$ is required measurable.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 48, Appendix A.7, Remark (b), dominant strategy case (subdomain property)

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- Remark (b) of Appendix A.7, subdomain property in the dominant strategy case (p. 48):
`E[∑_j s^j(X) 1_{X∈A}] ≤ Rev^{DS}(X 1_{X∈A}) ≤ Rev^{DS}(X)` for every (measurable) `A ⊆ ℝ^{kn}_+`
and every IC-DS and IR-DS mechanism `µ`, whenever the expectation on `A` is defined. -/
theorem subdomain_ds {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (Fin n → ι → ℝ≥0)) [IsProbabilityMeasure μ] (M : MechanismN n ι)
    (hM : IsAdmissibleDS M) (A : Set (Fin n → ι → ℝ≥0)) (hA : MeasurableSet A)
    (hDefined : (∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ) ≠ ⊤ ∨
      (∫⁻ x in A, ENNReal.ofReal (-sellerRevenue M x) ∂μ) ≠ ⊤) :
    ((∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) -
        ((∫⁻ x in A, ENNReal.ofReal (-sellerRevenue M x) ∂μ : ℝ≥0∞) : EReal) ≤
      (RevDS (lawOnN μ A) : EReal) ∧
    RevDS (lawOnN μ A) ≤ RevDS μ := by sorry

end MultiItemRev.MultiBuyer
