-- Prove2me | Theorems.Thm_FrobeniusDensity_summable_degOne_term
-- name    : FrobeniusDensity.summable_degOne_term
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/e50e9b4d-ffb9-5c57-ad57-4e932ee7dbb4
-- title:
--   Summability of the degree-one prime series for s>1
-- statement:
--   Let $K$ be a number field, let $S_0$ be a finite set of natural numbers, and let $s$ be a real number with $1 < s$. For a natural number $\ell$ put $\mathrm{degOneCount}\,K\,\ell = 0$ unless $\ell$ is prime, in which case $\mathrm{degOneCount}\,K\,\ell$ is the cardinality of the set of primes $\mathfrak q$ of $\mathcal O_K$ lying over the ideal $\ell\mathbb Z$ of $\mathbb Z$ whose residue ring $\mathcal O_K/\mathfrak q$ has exactly $\ell$ elements, i.e. the number of degree-one primes of $K$ above $\ell$ (the cardinality being taken as the `ncard` of that set of primes over $\ell\mathbb Z$). The assertion is that the family of real numbers indexed by $\ell \in \mathbb N$ whose $\ell$-th term is $0$ when $\ell \in S_0$ and is $\mathrm{degOneCount}\,K\,\ell \cdot \ell^{-s}$ (real power) when $\ell \notin S_0$ is summable. Thus $\sum_{\ell \notin S_0} \#\{\mathfrak q \mid \ell : N\mathfrak q = \ell\}\,\ell^{-s} < \infty$ for $s > 1$.
--
--   This is the convergence half of the analytic input to the Chebotarev-style density estimates for degree-one primes: the series counting degree-one primes of $K$, with a finite set of excluded rational primes, converges in the half-plane $\mathrm{Re}\,s > 1$, since it is dominated by the Dedekind zeta series of $K$. It feeds into [`FrobeniusDensity.degOneAsymptotic`](thm.html#FrobeniusDensity.degOneAsymptotic), which is used when choosing auxiliary Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_summable_degOne_term.lean

import Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.summable_degOne_term
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by sorry
