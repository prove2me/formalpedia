-- Prove2me | Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO
-- name    : FrobeniusDensity.degOneSum_add_log_isBigO
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/7f4f34d0-7eb0-5602-88a6-24588e141040
-- title:
--   Degree-one prime sum plus log(s-1) is bounded
-- statement:
--   Let $K$ be a number field (a field with a `NumberField` structure over $\mathbb{Q}$) and let $S_0$ be a finite set of natural numbers. For a natural number $\ell$, write $\mathrm{degOneCount}\,K\,\ell$ for the number of primes of $K$ of residue degree one above $\ell$: it is $0$ unless $\ell$ is prime, and for $\ell$ prime it is the cardinality of the set of prime ideals $\mathfrak{q}$ of $\mathcal{O}_K$ lying over the ideal $\ell\mathbb{Z}$ whose residue ring $\mathcal{O}_K/\mathfrak{q}$ has exactly $\ell$ elements. The assertion is that the real-valued function
--   $$s \mapsto \sum_{\ell}' \bigl[\ell \notin S_0\bigr]\,\mathrm{degOneCount}\,K\,\ell \cdot \ell^{-s} \; + \; \log(s-1),$$
--   where the unconditional sum runs over all natural numbers $\ell$ and the terms with $\ell \in S_0$ are replaced by $0$, is $O(1)$ along the filter of neighbourhoods of $1$ within the open interval $(1,\infty)$, i.e. as $s \to 1^+$ through real values $s>1$. Equivalently, the sum of $\ell^{-s}$ over degree-one primes of $K$ above rational primes outside $S_0$, counted with multiplicity, equals $\log\frac{1}{s-1} + O(1)$ as $s \to 1^+$.
--
--   This is the Landau-type asymptotic for the Dirichlet series of prime ideals of $K$, refined so that only primes of residue degree one above rational primes outside a prescribed finite set contribute: the primes above $S_0$ form a finite correction and the primes of residue degree at least two contribute a convergent series, so both are $O(1)$. It is obtained from the corresponding statement for the full prime sum via the splitting [`FrobeniusDensity.primeSum_eq_degOneSum_add`](thm.html#FrobeniusDensity.primeSum_eq_degOneSum_add), and feeds [`FrobeniusDensity.degOneAsymptotic`](thm.html#FrobeniusDensity.degOneAsymptotic) and the existence of infinitely many primes with prescribed splitting behaviour used in the construction of Taylor–Wiles primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_degOneSum_add_log_isBigO.lean

import Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Filter Topology Asymptotics

theorem FrobeniusDensity.degOneSum_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by sorry
