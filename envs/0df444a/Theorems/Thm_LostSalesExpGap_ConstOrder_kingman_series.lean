-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_kingman_series
-- name    : LostSalesExpGap.ConstOrder.kingman_series
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T08:03:39.116089+00:00
-- url     : https://prove2.me/theorems/6e4dc6e5-328f-4a1a-929f-2cb8df02a13f
-- title:
--   Lemma 3 (first two parts), p. 12 — Kingman's series for E[I^r_L] and E[I^r_∞] (Spitzer's identity)
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. copies of a nonnegative demand $D$ with finite positive mean $\mathbb E[D]$, and for an order level $r$ write
--   $$I^r_m=\max_{0\le j\le m}\Big(jr-\sum_{i=1}^jD_i\Big),\qquad I^r_\infty=\sup_{j\ge0}\Big(jr-\sum_{i=1}^jD_i\Big)\in[0,\infty].$$
--   Then for every $r\in[0,\mathbb E[D]]$ and every $m\ge1$,
--   $$\mathbb E[I^r_m]=\sum_{n=1}^m\frac1n\,\mathbb E\Big[\Big(nr-\sum_{i=1}^nD_i\Big)^+\Big],$$
--   and for every $r\in[0,\mathbb E[D])$,
--   $$\mathbb E[I^r_\infty]=\sum_{n=1}^\infty\frac1n\,\mathbb E\Big[\Big(nr-\sum_{i=1}^nD_i\Big)^+\Big]\qquad\text{in }[0,\infty].$$
--   These are the first two assertions of Lemma 3 of Xin and Goldberg (Theorems 1 and 4 of Kingman (1962)), a form of Spitzer's identity for the expected maximum of a random walk.
--
--   **Formalization note.** The model objects are those of the published `LostSalesExpGap_ConstOrder_ConstantOrder` definitions: $\mathbb E[I^r_m]$ is `EIL P r m` (a Bochner integral of the finite maximum), $\mathbb E[I^r_\infty]$ is `EIinf P r` (a lower integral in $[0,\infty]$), and the series index is shifted by one (the Lean summand at $n$ is the paper's term $n+1$). This is the part of milestone `lemma_3` that does not involve $r_\infty$, $\gamma$ or $\vartheta$.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Lemma 3 (first two displays), p. 12; Kingman, Some inequalities for the queue GI/G/1, Biometrika 49 (1962) 315-324, Theorems 1 and 4

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Lemma 3, first two parts, p. 12 (Theorems 1 and 4 of Kingman (1962), via Spitzer's identity).
For `r ∈ [0, E[D]]` and `m ≥ 1`, `E[I^r_m] = Σ_{n=1}^m (1/n) E[(n r − Σ_{i=1}^n D_i)^+]`; for
`r ∈ [0, E[D])`, `E[I^r_∞] = Σ_{n=1}^∞ (1/n) E[(n r − Σ_{i=1}^n D_i)^+]` in `[0, ∞]`. Sums over `n`
are shifted by one: the summand at `n` is the paper's term `n + 1`. -/
theorem kingman_series (P : CappedBaseStock.DemandLaw) :
    (∀ r : ℝ, 0 ≤ r → r ≤ CappedBaseStock.mean P → ∀ m : ℕ, 1 ≤ m →
      EIL P r m = ∑ n ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ r : ℝ, 0 ≤ r → r < CappedBaseStock.mean P →
      EIinf P r = ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
        ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ))
          ∂CappedBaseStock.demandPathLaw P) := by sorry

end LostSalesExpGap.ConstOrder
