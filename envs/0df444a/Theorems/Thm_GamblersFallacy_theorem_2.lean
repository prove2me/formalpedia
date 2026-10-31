-- Prove2me | Theorems.Thm_GamblersFallacy_theorem_2
-- name    : GamblersFallacy.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:45.576027+00:00
-- url     : https://prove2.me/theorems/12d0fddc-8fba-466f-9039-df77a3ae2b26
-- title:
--   Theorem 2 (corrected: $j=n$ term) — the exact form of $p_j(n)$
-- statement:
--   Let demands arrive at position $0$ and then independently with probability $p$ in each of the periods $1,\dots,n$, and let $p_j(n)=\mathbb E[\hat p_j(n)]$ be the expected empirical proportion of inter-arrival gaps of length $j$. Write $q=1-p$. For every horizon $n\ge1$, every gap length $j\ge1$ and every $p\in[0,1]$,
--   $$p_j(n)=\sum_{i=1}^{n-j}\binom{n-1-j}{i-1}p^iq^{n-1-i}\,\frac{p+i}{i+1}\;+\;\mathbf 1[j=n]\,p\,q^{n-1}.$$
--   For $j>n$ both sides are $0$.
--
--   This is the closed form of the finite-horizon bias when demand arrivals are independent; for $j=1$ it gives $p_1(n)<p$ and it is the starting point of the comparative statics in Proposition 2.
--
--   **Formalization Note** $p_j(n)$ is the expectation of the positional empirical proportion over the $2^n$ Bernoulli paths (`biasedEstimate n j p`); the sum is over `Finset.Icc 1 (n - j)`, empty for $j\ge n$, and its natural-number subtractions never truncate. Lean's $0^0=1$ makes the endpoint cases $p\in\{0,1\}$ the usual degenerate laws.
--
--   Differences from the source:
--   - correction: $p_j(n)=\sum_{i=1}^{n-j}\binom{n-1-j}{i-1}p^iq^{n-1-i}\frac{p+i}{i+1}$ for every $j$ → the term $\mathbf 1[j=n]\,p\,q^{n-1}$ is added; reason: at $n=2$, $j=2$, $p=1/3$ the estimate is $p_2(2)=qp=2/9$ while the printed sum is empty ($0$); the proof EC.2.1 drops the $i=0$ term, which is non-zero only for $j=n$
--   - generalization: $p\in(0,1)$ → $p\in[0,1]$; reason: the identity also holds at $p\in\{0,1\}$ (both sides are polynomials in $p$, with $0^0=1$), and on $(0,1)$ it is the source's claim
--   - encoding: an $n$-period horizon → hypothesis $1\le n$; reason: at $n=0$ the proportion is $0/0$, which the source never considers
--   - encoding: inter-arrival value $j$ of $Z\in\{1,2,\dots\}$ → hypothesis $1\le j$; reason: same range
--   - encoding: $p_j(n)$ defined in (1) through $\tau$ and $Z_1,Z_2,\dots$ → expectation of the positional empirical proportion over the $2^n$ paths `Fin n → Bool` as a finite weighted sum, $q$ written $1-p$; reason: the same random variable under the same law
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 2, p.13; proof EC.2.1, pp.ec1–ec3

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate

namespace GamblersFallacy

/-- **Theorem 2 (corrected: the `j = n` term) — the exact form of `p_j(n)`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 2, p.13 (proof EC.2.1,
pp.ec1–ec3): "The exact form of p_j(n) is given by
p_j(n) = Σ_{i=1}^{n−j} C(n − 1 − j, i − 1) p^i q^{n−1−i} (p + i)/(i + 1)."

For every horizon `n ≥ 1`, gap length `j ≥ 1` and `p ∈ [0, 1]`, with `q = 1 - p`,
`p_j(n) = Σ_{i=1}^{n−j} C(n−1−j, i−1) p^i q^{n−1−i} (p+i)/(i+1) + [j = n] p q^{n−1}`.

**Correction.** The printed sum misses the term `[j = n] p q^{n−1}` (the case of no arrival in
the periods `1, …, n − 1` and an arrival in period `n`, dropped as `i = 0` in EC.2.1).
Counterexample to the printed form: `n = 2`, `j = 2`, `p = 1/3` gives `p₂(2) = qp = 2/9`, while
the printed sum is empty. For `j > n` both sides are `0`.

**Formalization Note.** `p_j(n)` is `biasedEstimate n j p`, the expectation of the empirical
proportion over the `2ⁿ` Bernoulli paths. The sum ranges over `Finset.Icc 1 (n - j)`, empty for
`j ≥ n`; in it `n − 1 − j` and `n − 1 − i` never truncate. Endpoints `p ∈ {0, 1}` are included,
with Lean's `0 ^ 0 = 1`. -/
theorem theorem_2 (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    biasedEstimate n j p =
      (∑ i ∈ Finset.Icc 1 (n - j),
          ((n - 1 - j).choose (i - 1) : ℝ) * p ^ i * (1 - p) ^ (n - 1 - i) *
            ((p + (i : ℝ)) / ((i : ℝ) + 1))) +
        (if j = n then p * (1 - p) ^ (n - 1) else 0) := by sorry

end GamblersFallacy
