-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_3
-- name    : LostSalesExpGap.ConstOrder.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:26.52062+00:00
-- url     : https://prove2.me/theorems/ac5425ef-41f1-45cf-a92d-10003116b24d
-- title:
--   Lemma 3, p. 12 — Kingman's series for E[I^r_L], E[I^r_∞], and E[I^r∞_∞] − E[I^r∞_L] ≤ ((1−γ)eϑ(L+1))⁻¹γ^{L+1}
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. nonnegative demands with finite mean and strictly positive variance, $h,p>0$, and let $I^r_L=\max_{j=0,\dots,L}(jr-\sum_{i=1}^jD_i)$, $I^r_\infty=\sup_{j\ge0}(jr-\sum_{i=1}^jD_i)$. Let $r_\infty,\gamma,\vartheta$ be as in Sec. 2.3. Then:
--   1. for all $r\in[0,\mathbb E[D]]$ and $L\ge1$,
--   $$
--   \mathbb E[I^r_L]=\sum_{n=1}^L\frac1n\,\mathbb E\Big[\Big(nr-\sum_{i=1}^nD_i\Big)^+\Big];
--   $$
--   2. if in addition $r<\mathbb E[D]$,
--   $$
--   \mathbb E[I^r_\infty]=\sum_{n=1}^\infty\frac1n\,\mathbb E\Big[\Big(nr-\sum_{i=1}^nD_i\Big)^+\Big];
--   $$
--   3. for all $L\ge1$,
--   $$
--   \mathbb E[I^{r_\infty}_\infty]-\mathbb E[I^{r_\infty}_L]\le\big((1-\gamma)e\vartheta(L+1)\big)^{-1}\gamma^{L+1}.
--   $$
--
--   These are Theorems 1 and 4 of Kingman (1962), specialized to the queue with interarrival law $\mathcal D$ and constant service time $r$.
--
--   **Formalization Note** Item 2 is an identity in $[0,\infty]$ (lower integrals and an extended-real series). Item 3 is stated additively in $[0,\infty]$, $\mathbb E[I^{r_\infty}_\infty]\le\mathbb E[I^{r_\infty}_L]+((1-\gamma)e(L+1))^{-1}\vartheta^{-1}\gamma^{L+1}$, with $1/\vartheta=0$ when $\vartheta=\infty$. Sums are indexed from $0$ in Lean: the term at $n$ is the paper's term $n+1$. $L$ in items 1 and 3 is any horizon $\ge1$, not tied to the model's lead time; $h,p$ enter only through $r_\infty$.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 3, p. 12

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 3, p. 12 (Theorems 1 and 4 of Kingman (1962)). For `r ∈ [0, E[D]]` and `m ≥ 1`,
`E[I^r_m] = Σ_{n=1}^m (1/n) E[(n r − Σ_{i=1}^n D_i)^+]`; for `r ∈ [0, E[D])`,
`E[I^r_∞] = Σ_{n=1}^∞ (1/n) E[(n r − Σ_{i=1}^n D_i)^+]`; and
`E[I^{r∞}_∞] − E[I^{r∞}_m] ≤ ((1 − γ) e ϑ (m + 1))⁻¹ γ^{m+1}`. Sums over `n` are shifted by one:
the summand at `n` is the paper's term `n + 1`. -/
theorem lemma_3 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    (∀ r : ℝ, 0 ≤ r → r ≤ CappedBaseStock.mean P → ∀ m : ℕ, 1 ≤ m →
      EIL P r m = ∑ n ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ r : ℝ, 0 ≤ r → r < CappedBaseStock.mean P →
      EIinf P r = ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
        ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ))
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ m : ℕ, 1 ≤ m →
      EIinf P (rInf P c) ≤ ENNReal.ofReal (EIL P (rInf P c) m) +
        ENNReal.ofReal (((1 - gamma P c) * Real.exp 1 * ((m : ℝ) + 1))⁻¹ * varthetaInv P c *
          gamma P c ^ (m + 1))) := by sorry

end LostSalesExpGap.ConstOrder
