-- Prove2me | Theorems.Thm_GamblersFallacy_proposition_2_last_inequality
-- name    : GamblersFallacy.proposition_2_last_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:16.86561+00:00
-- url     : https://prove2.me/theorems/adcc37e4-d5d2-4d88-981c-19c87352b16e
-- title:
--   EC.2.2 (ii), last inequality — $\sum_{i=0}^m\binom{m}{i}p^iq^{m-i}\frac{mp+2}{i+2}\ge1$, strict for $m\ge1$
-- statement:
--   Let $m\in\mathbb N$, $p\in(0,1)$ and $q=1-p$, and set
--   $$S=\sum_{i=0}^{m}\binom{m}{i}p^iq^{m-i}\,\frac{mp+2}{i+2}.$$
--   Then
--
--   1. $S\ge1$;
--   2. if $m\ge1$, then $S>1$.
--
--   With $X\sim\mathrm{Binomial}(m,p)$, $S=\mathbb E[X+2]\,\mathbb E[1/(X+2)]$. Combined with the identity (EC.2)–(EC.3), the strict bound gives $p_1(n+1)>p_1(n)$ for $n\ge2$.
--
--   **Formalization Note** The sum is over `Finset.range (m + 1)`, and $q$ is written $1-p$.
--
--   Differences from the source:
--   - generalization: $S\ge1$ → $S\ge1$, and $S>1$ when $m\ge1$; reason: the strict bound is what the strict conclusion of Proposition 2 (ii) needs; the first conjunct is the printed claim for every $m$
--   - encoding: $\sum_{i=0}^m$ and $q$ → `Finset.range (m + 1)` and $1-p$; reason: same expression
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (ii), display "for the last inequality", p.ec5

import Mathlib

namespace GamblersFallacy

/-- **EC.2.2 (ii), the last inequality (strict for `m ≥ 1`).**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (ii), p.ec5: "For the last
inequality, we use the same result from (EC.1) above such that Σ_{i=0}^{m} C(m, i) p^i q^{m−i}
(mp+2)/(i+2) = (mp + 2) Σ_{i=0}^{m} C(m, i) p^i q^{m−i} 1/(i+2) = [Σ_{i=0}^{m} C(m, i) p^i
q^{m−i}(i + 2)] [Σ_{i=0}^{m} C(m, i) p^i q^{m−i} 1/(i+2)] ≥ 1."

For every `m` and `p ∈ (0, 1)`, with `q = 1 − p`,
`S = Σ_{i=0}^m C(m, i) p^i q^{m−i} (mp+2)/(i+2) ≥ 1`, and `S > 1` when `m ≥ 1`.

**Formalization Note.** The printed `≥ 1` is the first conjunct. The second conjunct (strict for
`m ≥ 1`) is what the strict conclusion of Proposition 2 (ii) uses; at `m = 0`, `S = 1`. -/
theorem proposition_2_last_inequality (m : ℕ) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    1 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2)) ∧
      (1 ≤ m → 1 < ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) * (((m : ℝ) * p + 2) / ((i : ℝ) + 2))) := by sorry

end GamblersFallacy
