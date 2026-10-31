-- Prove2me | Theorems.Thm_GamblersFallacy_proposition_2_derivative
-- name    : GamblersFallacy.proposition_2_derivative
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:25:53.003869+00:00
-- url     : https://prove2.me/theorems/a8673547-c2ba-4dda-a496-6d77ce93bbc2
-- title:
--   EC.2.2 (i) (corrected: $m\ge1$) — $p_1(n)/p$ and its derivative in $p$
-- statement:
--   Let $p_1(n)$ be the expected empirical proportion of consecutive arrivals over a horizon of $n$ periods after an initial arrival, with i.i.d. arrival probability $p$, and set $m=n-1$. For every $m\ge1$ and $p\in(0,1)$:
--
--   1. the ratio $p_1(n)/p$ has the binomial form
--   $$\frac{p_1(n)}{p}=\sum_{i=1}^{m}\binom{m-1}{i-1}p^{i-1}(1-p)^{m-i}\,\frac{p+i}{i+1};$$
--   2. the function $f(x)=p_1(n)(x)/x$ is differentiable at $p$ with
--   $$f'(p)=p^{-1}\left(\sum_{i=1}^{m}\binom{m-1}{i-1}p^{i-1}(1-p)^{m-i}\,\frac{mp+2}{i+1}-1\right).$$
--
--   Together with (EC.1), which shows the bracket is positive, this gives that $p_1(n)/p$ is strictly increasing in $p$, i.e. part (i) of Proposition 2.
--
--   **Formalization Note** The horizon is $n=m+1$, so $p_1(n)$ is `biasedEstimate (m + 1) 1`, the expectation over the Bernoulli paths. The derivative is stated as `HasDerivAt` of $x\mapsto p_1(m+1)(x)/x$ at $p$. Only the first and the last line of the printed chain for $f'(p)$ are stated; the intermediate lines are steps of the proof.
--
--   Differences from the source:
--   - correction: $m=n-1$ for every $n$ → $m\ge1$ (i.e. $n\ge2$); reason: at $n=1$ ($m=0$), $p_1(1)/p=1$ for every $p$, while the printed sum is empty ($0$) and the printed $f'(p)=-1/p\ne0$
--   - encoding: the horizon $n$ with $m=n-1$ → $m:\mathbb N$ and horizon $m+1$; reason: avoids natural-number subtraction, same instances
--   - encoding: the display $f'(p)=\dots$ → `HasDerivAt (fun x => p₁(m+1)(x)/x) (…) p`; reason: the printed derivative of $f$ at $p$
--   - encoding: $p_1(n)$ of (1) → expectation over the $2^n$ paths as a finite weighted sum; reason: the same random variable under the same law
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2 (i), display for p₁(n)/p and for f′(p), pp.ec3–ec4

import Mathlib
import Definitions.Def_GamblersFallacy_biasedEstimate

namespace GamblersFallacy

/-- **EC.2.2 (i) (corrected: `m ≥ 1`) — `p₁(n)/p` and its derivative in `p`.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, EC.2.2, proof of Proposition 2 (i),
pp.ec3–ec4, with `m = n − 1`:
"p₁(n)/p = Σ_{i=1}^{m} C(m − 1, i − 1) p^{i−1} q^{m−i} (p + i)/(i + 1). Let f(p) = p₁(n)/p, the
first order derivatives is f′(p) = … = p^{−1}(Σ_{i=1}^{m} C(m − 1, i − 1) p^{i−1}(1 − p)^{m−i}
(mp + 2)/(i + 1) − 1)".

For `m ≥ 1` and `p ∈ (0, 1)`, with `n = m + 1`:
1. `p₁(m+1)/p = Σ_{i=1}^m C(m−1, i−1) p^{i−1} (1−p)^{m−i} (p+i)/(i+1)`;
2. `f(x) = p₁(m+1)(x)/x` has derivative
   `p⁻¹ (Σ_{i=1}^m C(m−1, i−1) p^{i−1} (1−p)^{m−i} (mp+2)/(i+1) − 1)` at `p`.

**Formalization Note.** The horizon is `n = m + 1`, so `m ≥ 1` is `n ≥ 2` (the corrected range of
Proposition 2); at `m = 0` both displays are false (`p₁(1)/p = 1`, the sum is empty).
`p₁(n)` is `biasedEstimate (m + 1) 1`, the expectation over Bernoulli paths. The intermediate
lines of the printed derivative chain are not stated. -/
theorem proposition_2_derivative (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    biasedEstimate (m + 1) 1 p / p =
        ∑ i ∈ Finset.Icc 1 m,
          ((m - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (m - i) *
            ((p + (i : ℝ)) / ((i : ℝ) + 1)) ∧
      HasDerivAt (fun x : ℝ => biasedEstimate (m + 1) 1 x / x)
        (p⁻¹ * ((∑ i ∈ Finset.Icc 1 m,
          ((m - 1).choose (i - 1) : ℝ) * p ^ (i - 1) * (1 - p) ^ (m - i) *
            (((m : ℝ) * p + 2) / ((i : ℝ) + 1))) - 1)) p := by sorry

end GamblersFallacy
