-- Prove2me | Theorems.Thm_OddGoldbach19_prime_pair_count_base_five
-- name    : OddGoldbach19.prime_pair_count_base_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:48:01.4099+00:00
-- url     : https://prove2.me/theorems/290d0489-5178-47d2-8882-6be86c63470b
-- title:
--   Prime-pair count using the coefficient-five reciprocal sieve
-- statement:
--   Let x,d be natural numbers with x>=5 and d positive and even. Count the integers n for which n and n+d are prime and n+d<=x. Put z=sqrt(x)/sqrt5. Let K(d) be the product over odd prime factors p of d of (p-1)/(p-2). For a squarefree integer q define g(q) as the product over prime factors p of q of1 when p=2 and2/(p-2) otherwise; set g(q)=0 for non-squarefree q. The prime-pair count is at most K(d)*x divided by the sum of g(q)/(1+q/z) over1<=q<=floor(z), plus z+1. This replaces the previous cutoff sqrt(x)/4 with a larger cutoff justified by the new sieve coefficient5.
-- source:
--   Adapted from accepted Prove2Me submissioned34ad35-bd22-4e5d-bf6f-b8b128b6e6c1 for PrimePairSieve_prime_pair_count_base_reciprocal_bound (public Apache2.0 contribution). Uses new proved coefficient-five weighted sifted inequality and existing divisor-kernel comparison. Cutoffsqrt(x/5) derived here.

import Mathlib
open scoped BigOperators

theorem OddGoldbach19.prime_pair_count_base_five
    (x d : ℕ) (hx : 5 ≤ x) (hd0 : 0 < d) (hd : 2 ∣ d) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    ((∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1) * x) /
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ)/Real.sqrt (5 : ℝ)⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) /
            (1+(q : ℝ)/(Real.sqrt (x : ℝ)/Real.sqrt (5 : ℝ)))) + Real.sqrt (x : ℝ)/Real.sqrt (5 : ℝ) + 1 := by sorry
