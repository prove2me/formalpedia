-- Prove2me | Theorems.Thm_MinFracProphet_lemma_1
-- name    : MinFracProphet.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:23.553387+00:00
-- url     : https://prove2.me/theorems/0d4da9e7-0574-4455-9e20-38bd77f9b2c6
-- title:
--   Lemma 1: $\mathrm{OPT}(c,p)=\bigl(\sum_{i=1}^n c_i^q\bigr)^{1/q}$ with $q=-1/(p-1)$
-- statement:
--   Let $n\ge1$, $p>1$ and $q=-\frac1{p-1}$, and let $c=(c_1,\dots,c_n)$ have positive entries. Then the prophet's problem (2) has a minimizer, and its optimal value is
--   $$
--   \mathrm{OPT}(c,p)=\min_{x\in\Delta_n}\sum_{i=1}^n c_ix_i^p=\Bigl(\sum_{i=1}^n c_i^q\Bigr)^{1/q}.
--   $$
--
--   This closed form turns every question about the prophet's expected cost into a question about power means of the prices; it is the starting point of both bounds of Theorem 2.
--
--   **Formalization Note** The conclusion is stated as `IsLeast` of the set of costs of feasible allocations (the value is attained and is a lower bound), together with the equality for `OPT`, the real infimum.
--
--   Differences from the source:
--   - reading: for any c = (c_1,…,c_n) → every c_i > 0; reason: at c_i = 0 the power c_i^q (q < 0) is undefined, and Lean’s 0^q = 0 would make the formula false; the paper applies Lemma 1 only to prices c_i ≥ ℓ > 0
--   - encoding: sellers 1,…,n → sellers Fin n with 0 < n; reason: Lean convention, an index shift; n = 0 has no feasible allocation
--   - encoding: OPT(c,p) the optimal value of the minimization (2) → IsLeast of the image of the cost over the feasible set, and OPT (real infimum) equal to the value; reason: the minimum exists and equals the infimum
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Lemma 1, p.10 (restated p.20)

import Mathlib
import Definitions.Def_MinFracProphet_Model

namespace MinFracProphet

/-- **Lemma 1**, p.10 of J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet
Inequalities for Sequential Procurement*, author manuscript (sha256 672fa87c…79125d3).

For `n ≥ 1`, `p > 1`, `q = -1/(p-1)` and prices `c = (c_1, …, c_n)` with every `c_i > 0`, the
minimum of the prophet's problem (2) is attained and
`OPT(c,p) = (∑_{i=1}^n c_i^q)^{1/q}`.

**Formalization Note** Sellers are `Fin n` with `0 < n` (R2). The page says "for any `c`"; at
`c_i = 0` the power `c_i^q` (`q < 0`) is undefined, and Lean's `0 ^ q = 0` would make the formula
false, so the prices are positive (R6), which is how the paper uses the lemma (`c_i ≥ ℓ > 0`).
`IsLeast` asserts that the value is attained by a feasible allocation and is a lower bound on the
cost of every feasible allocation; `OPT` is the real infimum, so the second conjunct follows from
the first and is stated for readability. -/
theorem lemma_1 (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (q : ℝ) (hq : q = -1 / (p - 1))
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    IsLeast (procCost p c '' simplex n) ((∑ i, c i ^ q) ^ (1 / q)) ∧
      OPT p c = (∑ i, c i ^ q) ^ (1 / q) := by sorry

end MinFracProphet
