-- Prove2me | Theorems.Thm_LL_JSConstants_twin_prime_tail_ge
-- name    : LL_JSConstants.twin_prime_tail_ge
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-23T17:43:00.304888+00:00
-- url     : https://prove2.me/theorems/5fd692c1-cee5-4646-90f8-0afe8612b24f
-- title:
--   Lower bound $0.996044$ for the tail of the twin prime product over primes $p>50$
-- statement:
--   With $P$ the set of primes $p>2$ and $F=\{p\in P:p<51\}$, the unconditional product over $P\setminus F$ satisfies $\prod_{p>50,\ p\text{ prime}}\Bigl(1-\frac{1}{(p-1)^2}\Bigr)\ge 0.996044$, where the product is the infinite product $\prod'$ of real numbers (taken to be $1$ if the family were not multipliable).
-- source:
--   Johnston and Starichkova, arXiv:2208.01229v3, page 3, the twin prime constant $C_2$ in $U_N$; sibling file on $C_2$.

import Mathlib

namespace LL_JSConstants
theorem twin_prime_tail_ge :
    (0.996044 : ℝ) ≤ ∏' x : ((((Finset.range 51).subtype (fun p : ℕ => p.Prime ∧ 2 < p) :
        Finset {p : ℕ // p.Prime ∧ 2 < p}) : Set {p : ℕ // p.Prime ∧ 2 < p})ᶜ :
        Set {p : ℕ // p.Prime ∧ 2 < p}),
      (1 - 1 / ((((x : {p : ℕ // p.Prime ∧ 2 < p}) : ℕ) : ℝ) - 1) ^ 2) := by sorry
end LL_JSConstants
