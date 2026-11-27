-- Prove2me | Theorems.Thm_GamblersFallacy_Supplement_theorem_1
-- name    : GamblersFallacy.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:12:59.049232+00:00
-- url     : https://prove2.me/theorems/d9b69474-62a2-4bd7-bf4a-f2aca7ee6980
-- title:
--   Theorem 1 (corrected: $n>\ell$, $P[E_{k\ell}(0)]<1$) — the finite-horizon estimate of $E_{k\ell}$ is biased downwards
-- statement:
--   Let demand inter-arrival times be i.i.d. with law $P(Z=j)=p_j>0$ for $j=1,\dots,J$, $\sum_j p_j=1$. The arrivals follow the general Markov chain of §3.1, which starts with an arrival at position $0$. Let $k\le\ell$. For a horizon $n\ge\ell$, let $\hat p_{E_{k\ell}}(n)$ be the fraction of arrivals at the positions $0,\dots,n-\ell$ that are followed by at least $k$ arrivals in the next $\ell$ periods. Let $P[E_{k\ell}(0)]$ be the true probability of at least $k$ arrivals in the $\ell$ periods after an arrival. Then:
--
--   1. for every horizon $n\ge\ell$,
--   $$
--   \mathbb E\big[\hat p_{E_{k\ell}}(n)\big]\le P[\chi(E_{k\ell}(0))=1];
--   $$
--   2. if $P[\chi(E_{k\ell}(0))=1]<1$, then for every horizon $n>\ell$,
--   $$
--   \mathbb E\big[\hat p_{E_{k\ell}}(n)\big]< P[\chi(E_{k\ell}(0))=1].
--   $$
--
--   This is the gambler's fallacy for general streak events in a renewal demand process: the empirical frequency computed over a finite history underestimates the probability of a streak. Proposition 1 is the case $k=\ell=1$, and (with $k=1$, $\ell=W$) it is the input to the comparison of delay policies in §4.1.
--
--   **Formalization Note** The law is `InterArrivalLaw` with the hypothesis $p_j>0$ on $\{1,\dots,J\}$. Expectations are finite weighted sums over the $2^n$ arrival patterns under the renewal law of §3.1.
--
--   Differences from the source:
--   - correction: $\mathbb E[\hat p_{E_{k\ell}}(n)]<P[\chi(E_{k\ell}(0))=1]$ for all $n$ → the weak inequality for every $n\ge\ell$, and the strict one for $n>\ell$ when $P[E_{k\ell}(0)]<1$; reason: at $n=\ell$ the window is $\{0\}$, so $\hat p_{E_{k\ell}}(\ell)=\chi(E_{k\ell}(0))$ and the two sides are equal for every law. When $P[E_{k\ell}(0)]=1$ (e.g. $k=1$, $J\le\ell$, or $J=1$), $\hat p=1$ on every path of positive probability and the sides are equal again. An exact enumeration over $J\le4$ and $\ell\le n\le 10$ found equality in exactly these cases and strict inequality in all others
--   - generalization: $1\le k\le\ell$ (at least $k$ arrivals) → $k\le\ell$, $k=0$ allowed; reason: for $k=0$ the event is sure and both sides equal $1$, so part 1 holds and part 2 is vacuous; for $k\ge1$ it is the source's claim
--   - encoding: the general Markov chain with hazards $p_j/\sum_{i\ge j}p_i$ started at state "1" → the renewal law of the arrival pattern, $\prod p_{\text{gap}}\cdot P(Z>n-s_m)$, as a finite weighted sum over `Fin n → Bool`; reason: the two laws are equal, since the hazards along a gap of length $j$ multiply to $p_j$
--   - encoding: $\ell\le n-t$ in the definition of $E_{k\ell}(t)$ → horizons $n\ge\ell$; reason: the source's own range at $t=0$, where the estimate is defined
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 1, p.12 (proof p.12); E_kℓ(t), p.11; the general Markov chain, pp.9–10

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw
import Definitions.Def_GamblersFallacy_Supplement_EventEstimate

namespace GamblersFallacy.Supplement

/-- **Theorem 1 (corrected: `n > ℓ`, `P[E_kℓ(0)] < 1`) — the finite-horizon estimate of
`E_kℓ` is biased downwards.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 1, p.12: "For any general Markov
chain starting at state "1", over a finite horizon n, we have
E[p̂_{E_kℓ}(n)] := E[Σ_{i=0}^{n−ℓ} B_n(i)χ(E_kℓ(i)) / Σ_{i=0}^{n−ℓ} B_n(i)] < P[χ(E_kℓ(0)) = 1],
∀n."

For an inter-arrival law with `p_j > 0` for `j = 1, …, J` and `k ≤ ℓ`:
1. `E[p̂_{E_kℓ}(n)] ≤ P[E_kℓ(0)]` for every horizon `n ≥ ℓ`;
2. `E[p̂_{E_kℓ}(n)] < P[E_kℓ(0)]` for every `n > ℓ` whenever `P[E_kℓ(0)] < 1`.

**Correction.** At `n = ℓ` the sums have the single term `i = 0`, so `p̂ = χ(E_kℓ(0))` and the two
sides are equal; if `P[E_kℓ(0)] = 1` (e.g. `k = 1 ≤ J ≤ ℓ`) then `p̂ = 1` on every path and the
two sides are equal. Strictness is stated off these cases; part 1 covers them.

**Formalization Note.** The chain is the renewal law `L.renewalWeight` of §3.1; expectations are
finite sums over the `2ⁿ` arrival patterns; `ℓ ≤ n` is the source's range `k ≤ ℓ ≤ n − t`
at `t = 0`. The count `k = 0` (the sure event) is allowed: both sides are then `1`. -/
theorem theorem_1 (L : InterArrivalLaw) (hpos : ∀ j ∈ Finset.Icc 1 L.J, 0 < L.p j)
    (k l : ℕ) (hkl : k ≤ l) :
    (∀ n : ℕ, l ≤ n → expectedEventEstimate L n k l ≤ eventProb L k l) ∧
    (∀ n : ℕ, l < n → eventProb L k l < 1 →
      expectedEventEstimate L n k l < eventProb L k l) := by sorry

end GamblersFallacy.Supplement
