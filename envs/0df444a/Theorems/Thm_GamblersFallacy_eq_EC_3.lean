-- Prove2me | Theorems.Thm_GamblersFallacy_eq_EC_3
-- name    : GamblersFallacy.eq_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:52.419668+00:00
-- url     : https://prove2.me/theorems/3657ce1f-fd87-4375-b538-d4bad237f855
-- title:
--   (EC.2)–(EC.3) (corrected: equality in (EC.2)) — the increment $p_1(n+1)-p_1(n)$
-- statement:
--   Let $p_1(n)$ be the expected empirical proportion of consecutive arrivals over a horizon of $n$ periods after an initial arrival, with i.i.d. arrival probability $p$. Let $n\ge2$, $m=n-1$, $p\in(0,1)$ and $q=1-p$. Then
--   $$p_1(n+1)-p_1(n)=\frac{pq}{mq}\left[\sum_{i=0}^{m}\binom{m}{i}p^iq^{m-i}\,\frac{mp+2}{i+2}-1\right].$$
--
--   With the last inequality of EC.2.2 (ii), which makes the bracket positive, this shows that $p_1(n)$ is strictly increasing in $n\ge2$, i.e. part (ii) of Proposition 2.
--
--   **Formalization Note** The horizon is $n=m+1$, so the statement is about `biasedEstimate (m + 2) 1 p - biasedEstimate (m + 1) 1 p`. The factor $pq/(mq)$ is kept as printed.
--
--   Differences from the source:
--   - correction: $p_1(n+1)-p_1(n)>$ (the expression of (EC.2)) $=\dots=$ (EC.3) → $p_1(n+1)-p_1(n)=$ (EC.3); reason: the two sides are equal ($\binom{m-1}{i}=\binom{m}{i}\frac{m-i}{m}$, $q^{m-i-1}=q^{m-i}/q$); at $n=2$, $p=1/3$ both are $1/81$, so the strict inequality is false
--   - reading: $m=n-1$ → $m\ge1$; reason: the printed factor $pq/(mq)$ is defined only for $m\ge1$
--   - encoding: the horizon $n$ with $m=n-1$ → $m:\mathbb N$ and horizons $m+1$, $m+2$; reason: avoids natural-number subtraction, same instances
--   - encoding: $p_1(n)$ of (1) → expectation over the $2^n$ paths as a finite weighted sum; reason: the same random variable under the same law
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (ii), (EC.2)–(EC.3), p.ec4

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate

namespace GamblersFallacy

/-- **(EC.2)–(EC.3) (corrected: equality in (EC.2)) — the increment `p₁(n + 1) − p₁(n)`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (ii), (EC.2)–(EC.3), p.ec4, with
`m = n − 1`: "p₁(n + 1) − p₁(n) = … > Σ_{i=0}^{m} C(m, i) p^{i+1} q^{m−i} (p+i+1)/(i+2)
(1 − (m−i)/(mq)) = … = pq/(mq) [Σ_{i=0}^{m} C(m, i) p^i q^{m−i} (mp+2)/(i+2) − 1] (EC.3)".

For `m ≥ 1` (`n = m + 1 ≥ 2`) and `p ∈ (0, 1)`, with `q = 1 − p`,
`p₁(m+2) − p₁(m+1) = (pq/(mq)) [Σ_{i=0}^m C(m, i) p^i q^{m−i} (mp+2)/(i+2) − 1]`.

**Correction.** The printed chain has a strict `>` between `p₁(n + 1) − p₁(n)` and (EC.3); the two
are equal (`C(m−1, i) = C(m, i)(m−i)/m`, `q^{m−i−1} = q^{m−i}/q`). Counterexample to `>`:
`n = 2`, `p = 1/3`, both sides are `1/81`.

**Formalization Note.** `m ≥ 1` because the factor `pq/(mq)` is defined only for `m ≥ 1`.
`p₁(n)` is `biasedEstimate n 1`. The factor `pq/(mq)` is kept as printed. -/
theorem eq_EC_3 (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    biasedEstimate (m + 2) 1 p - biasedEstimate (m + 1) 1 p =
      p * (1 - p) / ((m : ℝ) * (1 - p)) *
        ((∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) *
              (((m : ℝ) * p + 2) / ((i : ℝ) + 2))) - 1) := by sorry

end GamblersFallacy
