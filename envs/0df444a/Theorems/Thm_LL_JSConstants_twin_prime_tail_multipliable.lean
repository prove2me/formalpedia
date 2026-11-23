-- Prove2me | Theorems.Thm_LL_JSConstants_twin_prime_tail_multipliable
-- name    : LL_JSConstants.twin_prime_tail_multipliable
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:42:41.595867+00:00
-- url     : https://prove2.me/theorems/238c4096-94cd-4594-9eb3-52b93df8248a
-- title:
--   Convergence of the tail of the twin prime product over primes $p>50$
-- statement:
--   Let $P$ be the set of primes $p>2$ and $F=\{p\in P: p<51\}$. The family $\bigl(1-\frac{1}{(p-1)^2}\bigr)_{p\in P\setminus F}$ of real numbers is multipliable, that is, the unconditional infinite product $\prod_{p>50,\ p\text{ prime}}\bigl(1-\frac{1}{(p-1)^2}\bigr)$ converges in $\mathbb{R}$ in the sense of finite partial products along the filter of finite subsets.
-- source:
--   Johnston and Starichkova, arXiv:2208.01229v3, page 3, the twin prime constant $C_2$ in $U_N$; sibling file on $C_2$.

import Mathlib

namespace LL_JSConstants
theorem twin_prime_tail_multipliable :
    Multipliable (fun x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}) =>
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2)) := by sorry
end LL_JSConstants
