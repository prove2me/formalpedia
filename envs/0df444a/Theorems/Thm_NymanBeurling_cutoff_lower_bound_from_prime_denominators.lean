-- Prove2me | Theorems.Thm_NymanBeurling_cutoff_lower_bound_from_prime_denominators
-- name    : NymanBeurling.cutoff_lower_bound_from_prime_denominators
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:45:59.597757+00:00
-- url     : https://prove2.me/theorems/80517113-89cb-4173-bd4a-a017fc9d0907
-- title:
--   A lower bound on the cutoff of a rational Nyman–Beurling certificate
-- statement:
--   If the rational certificate has cost less than $1/(J+1)$, select any finite set $P$ of coefficient indices $k$ for which $p=k+2$ is prime and $8p^2+24\le J+1$. Then its cutoff satisfies $H+1>(J+1)(1+|P|/2)^2$. This is an unconditional necessary resource bound, uniform over the chosen coefficients.
-- source:
--   Independent consequence of the prime-coefficient obstruction and the exact tail majorant in the Bagchi discrete Nyman–Beurling criterion. https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem NymanBeurling.cutoff_lower_bound_from_prime_denominators (c : ℕ →₀ ℚ) (J H : ℕ) (P : Finset ℕ)
    (haccuracy : ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1 / (J + 1 : ℚ))
    (hprime : ∀ k ∈ P, (k+2).Prime)
    (hsize : ∀ k ∈ P, 8*((k : ℚ)+2)^2+24 ≤ (J+1 : ℚ)) :
    (J+1 : ℚ) * (1+(P.card : ℚ)/2)^2 < (H+1 : ℚ) := by sorry
