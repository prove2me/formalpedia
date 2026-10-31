-- Prove2me | Theorems.Thm_GamblersFallacy_proposition_2
-- name    : GamblersFallacy.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:57.164018+00:00
-- url     : https://prove2.me/theorems/ad7cba60-b56a-45a3-87f7-b13f55ee163c
-- title:
--   Proposition 2 (corrected: $n\ge2$) — the relative bias $(p-p_1(n))/p$ is strictly decreasing in $p$ and in $n$
-- statement:
--   A demand arrives at time $0$, and then independently with probability $p\in(0,1)$ in each of the periods $1,\dots,n$. Let $p_1(n)=\mathbb E[\hat p_1(n)]$ be the expected empirical proportion of arrivals (among those at positions $0,\dots,n-1$) that are immediately followed by another arrival. The **relative bias** is
--   $$\frac{p-p_1(n)}{p}.$$
--   Then:
--
--   1. for every $n\ge2$, the relative bias is strictly decreasing in $p$ on $(0,1)$;
--   2. for every $p\in(0,1)$, the relative bias is strictly decreasing in $n$ on $\{n\in\mathbb N:n\ge2\}$.
--
--   The gambler's fallacy bias of the finite-horizon estimate is therefore largest, relative to $p$, for rare demand and short horizons, which is the regime of long-tail items.
--
--   **Formalization Note** $p_1(n)$ is `biasedEstimate n 1 p`, the expectation of the positional empirical proportion over the $2^n$ Bernoulli paths of the periods $1,\dots,n$. Both monotonicity claims are `StrictAntiOn`.
--
--   Differences from the source:
--   - correction: (i) and (ii) "for all $n$" → $n\ge2$; reason: at $n=1$, $\hat p_1(1)=G(0)$, so $p_1(1)=p$ and the relative bias is $0$ for every $p$, so (i) fails at $n=1$ under the strict reading adopted below (a constant is not strictly decreasing), and (ii) fails at $n=1$ under either reading: at $p=1/3$ the bias rises from $0$ at $n=1$ to $(1-p)/2=1/3$ at $n=2$
--   - reading: "decreasing" → strictly decreasing (`StrictAntiOn`); reason: the proof shows $f'(p)>0$ and concludes $(p-p_1(n+1))/p<(p-p_1(n))/p$
--   - reading: "for all $p$" → $p\in(0,1)$; reason: the paper's arrival probability is $p\in(0,1)$ (p.5) and the relative bias divides by $p$
--   - encoding: $p_1(n)$ of (1) → expectation over the $2^n$ paths `Fin n → Bool` as a finite weighted sum; reason: the same random variable under the same law
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Proposition 2, p.14; proof EC.2.2, pp.ec3–ec5

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate

namespace GamblersFallacy

/-- **Proposition 2 (corrected: `n ≥ 2`) — the relative bias is strictly decreasing in `p` and in
`n`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Proposition 2, p.14 (proof EC.2.2,
pp.ec3–ec5): "The relative bias between p and p₁(n), defined as (p − p₁(n))/p, is (i) decreasing
in p for all n, and (ii) decreasing in n for all p."

1. For every `n ≥ 2`, `p ↦ (p − p₁(n))/p` is strictly decreasing on `(0, 1)`.
2. For every `p ∈ (0, 1)`, `n ↦ (p − p₁(n))/p` is strictly decreasing on `{n ∈ ℕ | n ≥ 2}`.

**Correction.** "For all n" is corrected to `n ≥ 2`: at `n = 1`, `p̂₁(1) = G(0)`, so `p₁(1) = p`
and the relative bias is `0` for every `p` (not decreasing in `p`), while at `n = 2` it is
`(1 − p)/2 > 0` (so it increases from `n = 1` to `n = 2`).

**Formalization Note.** "Decreasing" is read as strict (the proof shows `f′(p) > 0` and concludes
`(p − p₁(n+1))/p < (p − p₁(n))/p`); `p ∈ (0, 1)` as on p.5. `p₁(n)` is `biasedEstimate n 1 p`,
the expectation of the empirical proportion `p̂₁(n)` over the `2ⁿ` Bernoulli(`p`) paths of the
periods `1, …, n` after the initial arrival at `0`. -/
theorem proposition_2 :
    (∀ n : ℕ, 2 ≤ n →
      StrictAntiOn (fun p : ℝ => (p - biasedEstimate n 1 p) / p) (Set.Ioo 0 1)) ∧
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
      StrictAntiOn (fun n : ℕ => (p - biasedEstimate n 1 p) / p) {n : ℕ | 2 ≤ n}) := by sorry

end GamblersFallacy
