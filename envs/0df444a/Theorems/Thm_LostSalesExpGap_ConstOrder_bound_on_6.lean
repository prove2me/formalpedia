-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_bound_on_6
-- name    : LostSalesExpGap.ConstOrder.bound_on_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:36.583026+00:00
-- url     : https://prove2.me/theorems/3171d927-13ad-430b-bfbc-1634dd534210
-- title:
--   Sec. 3, p. 13 — the term (6) is at most h(E[D] − r∞)(1 − γ)⁻¹γ^{L+1}
-- statement:
--   In the lost-sales model with i.i.d. nonnegative demand of finite mean and strictly positive variance and costs $h,p>0$, let $r_\infty$, $r_L$, $\gamma$ and $I^r_L=\max_{j=0,\dots,L}(jr-\sum_{i=1}^jD_i)$ be as above. Then for every $L\ge1$ the quantity
--   $$
--   (6)\qquad h\big(\mathbb E[I^{r_\infty}_L]-\mathbb E[I^{r_L}_L]\big)-p\,(r_\infty-r_L)
--   $$
--   satisfies
--   $$
--   h\big(\mathbb E[I^{r_\infty}_L]-\mathbb E[I^{r_L}_L]\big)-p\,(r_\infty-r_L)\le h\big(\mathbb E[D]-r_\infty\big)(1-\gamma)^{-1}\gamma^{L+1}.
--   $$
--
--   Together with Lemma 3 this bounds the right-hand side of (5).
--
--   **Formalization Note** All quantities are finite reals; $(1-\gamma)^{-1}$ is finite because $\gamma<1$ (a separate milestone), which is not assumed. $L$ is any horizon $\ge1$.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 3, proof of Theorem 1, p. 13 (bound on (6), p. 12)

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Sec. 3, p. 13 (proof of Theorem 1): the quantity (6),
`h(E[I^{r∞}_m] − E[I^{r_m}_m]) − p(r∞ − r_m)`, is at most `h(E[D] − r∞)(1 − γ)⁻¹ γ^{m+1}`,
for every `m ≥ 1`. -/
theorem bound_on_6 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ∀ m : ℕ, 1 ≤ m →
      c.h * (EIL P (rInf P c) m - EIL P (rL P c m) m) - c.p * (rInf P c - rL P c m) ≤
        c.h * (CappedBaseStock.mean P - rInf P c) * (1 - gamma P c)⁻¹ * gamma P c ^ (m + 1) := by sorry

end LostSalesExpGap.ConstOrder
