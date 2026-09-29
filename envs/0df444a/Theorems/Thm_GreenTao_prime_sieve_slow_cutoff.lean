-- Prove2me | Theorems.Thm_GreenTao_prime_sieve_slow_cutoff
-- name    : GreenTao.prime_sieve_slow_cutoff
-- status  : Open
-- author  : @davidnet
-- created : 2026-09-06T02:30:19.315531+00:00
-- url     : https://prove2.me/theorems/0faffcbc-82e1-4c5b-a4fe-4a1a9cc969e4
-- title:
--   Pseudorandom prime majorant for sufficiently slow cutoffs
-- statement:
--   Fix $k\ge3$ and prime integers $M_n\to\infty$. There is an integer-valued upper cutoff $u_n\to\infty$ with the following property. For every sequence of natural numbers $w_n\to\infty$ satisfying $w_n\le u_n$ for all $n$, set
--
--   $$W_n=\prod_{p\le w_n}p.$$
--
--   There exists a nonnegative $k$-pseudorandom family $\nu_n$ on $\mathbb Z/M_n\mathbb Z$ such that, for all sufficiently large $n$,
--
--   $$F_{k,W_n,M_n}(x)\le\nu_n(x)\qquad\text{for every }x\in\mathbb Z/M_n\mathbb Z.$$
--
--   Here $F$ is the scaled prime-only weight on $[\epsilon_k M_n,2\epsilon_k M_n]$, with scaling $1/(k2^{k+5})$ and $\epsilon_k=1/(2^k(k+4)!)$. Pseudorandomness includes asymptotic mean one, the $(k2^{k-1},3k-4,k)$ linear forms condition, and the $2^{k-1}$ correlation condition of Green–Tao Definitions 3.1–3.3.
--
--   This formulates the phrase “sufficiently slowly growing” in Proposition 9.1 by an upper cutoff. It permits imposing additional slow-growth requirements on the same $w_n$. Neither positive mean for the prime weight nor a diagonal moment bound is included. Monotonicity of $w_n$ is not required; it must tend to infinity and stay below the cutoff. Nonnegativity of $\nu_n$ holds for every index, whereas domination is only eventual.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §9, Proposition 9.1, using the sufficiently slowly growing function w(N) introduced before it; Definition 9.3, Lemmas 9.4 and 9.7, Propositions 9.8 and 9.10. The upper-cutoff formulation makes the source slow-growth quantifiers explicit along a prescribed sequence of prime moduli.

import Definitions.Def_GreenTao_PrimeWeight

open Filter

theorem GreenTao.prime_sieve_slow_cutoff
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) :
    ∃ u : ℕ → ℕ, Tendsto u atTop atTop ∧
      ∀ w : ℕ → ℕ, Tendsto w atTop atTop → (∀ n, w n ≤ u n) →
        ∃ ν : GreenTao.Family M, GreenTao.Pseudorandom k M ν ∧
          ∀ᶠ n in atTop, ∀ x : ZMod (M n : ℕ),
            GreenTao.primeWeight k (primorial (w n)) x ≤ ν n x := by sorry
