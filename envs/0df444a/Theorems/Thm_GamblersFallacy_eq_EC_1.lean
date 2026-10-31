-- Prove2me | Theorems.Thm_GamblersFallacy_eq_EC_1
-- name    : GamblersFallacy.eq_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:13.598024+00:00
-- url     : https://prove2.me/theorems/3d169f19-3c2a-4860-924a-1d418a9a58a4
-- title:
--   (EC.1) (corrected: $m\ge1$) — $(mp+2)\sum_{i=1}^m\rho_i/(i+1)>1$
-- statement:
--   Let $m\ge1$ and $p\in(0,1)$, and let
--   $$\rho_i=\binom{m-1}{i-1}p^{i-1}(1-p)^{m-i},\qquad i=1,\dots,m,$$
--   be the probabilities of $1+X$ for $X\sim\mathrm{Binomial}(m-1,p)$. Then
--   $$(mp+2)\sum_{i=1}^{m}\frac{\rho_i}{i+1}>1.$$
--
--   This is the positivity of the bracket in the derivative of $p_1(n)/p$ (EC.2.2 (i)), hence the strict monotonicity of the relative bias in $p$.
--
--   **Formalization Note** The weights $\rho_i$ are written inline; the sum is over `Finset.Icc 1 m`.
--
--   Differences from the source:
--   - correction: $m=n-1$ for every $n$ → $m\ge1$; reason: at $m=0$ ($n=1$) the sum is empty and the left side is $0<1$
--   - encoding: $\rho_i$ and $\sum_{i=1}^m$ → written inline over `Finset.Icc 1 m`; reason: same expression
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (i), (EC.1), p.ec4

import Mathlib

namespace GamblersFallacy

/-- **(EC.1) (corrected: `m ≥ 1`) — `(mp + 2) Σ ρ_i/(i + 1) > 1`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (i), (EC.1), p.ec4: "we denote
ρ_i = C(m − 1, i − 1) p^{i−1}(1 − p)^{m−i} as the probability in the Binomial distribution
B(m − 1, p) … Then we show f′(p) > 0 by Σ_{i=1}^{m} C(m − 1, i − 1) p^{i−1}(1 − p)^{m−i}
(mp+2)/(i+1) = (mp + 2) Σ_{i=1}^{m} ρ_i 1/(i+1) > 1".

For `m ≥ 1` and `p ∈ (0, 1)`, with `ρ_i = C(m−1, i−1) p^{i−1} (1−p)^{m−i}`,
`(mp + 2) Σ_{i=1}^m ρ_i/(i+1) > 1`.

**Formalization Note.** `m ≥ 1`: at `m = 0` the sum is empty and the left side is `0`. The
weights `ρ_i` are written inline. -/
theorem eq_EC_1 (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 < ((m : ℝ) * p + 2) *
      ∑ i ∈ Finset.Icc 1 m,
        ((m - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (m - i) / ((i : ℝ) + 1) := by sorry

end GamblersFallacy
