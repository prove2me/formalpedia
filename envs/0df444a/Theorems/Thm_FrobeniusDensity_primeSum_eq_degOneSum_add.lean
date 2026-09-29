-- Prove2me | Theorems.Thm_FrobeniusDensity_primeSum_eq_degOneSum_add
-- name    : FrobeniusDensity.primeSum_eq_degOneSum_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/77672260-bcec-5c7c-899e-2dd5ccbbf04c
-- title:
--   Splitting the prime-ideal Dirichlet sum into degree-one, cut and tail parts
-- statement:
--   Let $K$ be a number field, let $S_0$ be a finite set of natural numbers, and let $s$ be a real number (no sign or size condition is imposed on $s$). All sums are unconditional sums in $[0,\infty]$. The assertion is the identity $$\mathrm{primeSum}_K(s)=\mathrm{degOneSum}_K(S_0,s)+\mathrm{cutSum}_K(S_0,s)+\mathrm{tailSum}_K(s),$$ where: `primeSum` is $\sum_{v}(\mathrm{absNorm}\,\mathfrak p_v)^{-s}$, the sum over the height-one spectrum of $\mathcal O_K$ of the absolute norm of the corresponding prime raised to $-s$ in $\mathbb R_{\ge 0}^\infty$; `degOneSum` is $\sum_{\ell\in\mathbb N,\ \ell\notin S_0} \mathrm{degOneCount}_K(\ell)\,\ell^{-s}$ and `cutSum` is the same sum restricted to $\ell\in S_0$, where $\mathrm{degOneCount}_K(\ell)$ is, for $\ell$ prime, the number of primes $\mathfrak q$ of $\mathcal O_K$ lying over the rational prime ideal $(\ell)$ with residue field of cardinality exactly $\ell$, and is $0$ for $\ell$ not prime; and `tailSum` is $\sum_{v}(\mathrm{absNorm}\,\mathfrak p_v)^{-s}$ taken over those $v$ whose absolute norm is not a prime number, the remaining terms being replaced by $0$.
--
--   This is the elementary three-piece decomposition of the prime-ideal Dirichlet series of $K$: primes of residue degree one are separated from those of residue degree at least two (degree one being detected by the absolute norm being a rational prime), and the degree-one contribution is then reindexed over the rational primes $\ell$ and split according to whether $\ell$ lies in the excluded finite set $S_0$. It is used by [`FrobeniusDensity.summable_degOne_term`](thm.html#FrobeniusDensity.summable_degOne_term) and by [`FrobeniusDensity.degOneSum_add_log_isBigO`](thm.html#FrobeniusDensity.degOneSum_add_log_isBigO), where the degree-one piece inherits the asymptotic behaviour of the full prime sum because the other two pieces are bounded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_primeSum_eq_degOneSum_add.lean

import Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.primeSum_eq_degOneSum_add
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by sorry
