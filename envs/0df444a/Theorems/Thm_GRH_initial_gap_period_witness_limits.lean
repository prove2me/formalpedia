-- Prove2me | Theorems.Thm_GRH_initial_gap_period_witness_limits
-- name    : GRH.initial_gap_period_witness_limits
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:45.235205+00:00
-- url     : https://prove2.me/theorems/b08329d5-e28c-4934-8a44-2bd94542d011
-- title:
--   A passing initial-gap witness has gap at most six, totient at most thirteen and prime factors at most five
-- statement:
--   Suppose a modulus $Q>2$ and a cutoff $M$ satisfy the initial-gap witness inequality at left edge $a\le1$, and all integers from $2$ through $M$ share a prime with $Q$. Then $M\le6$, $\varphi(Q)\le13$, and every prime factor of $Q$ is at most five.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient

theorem GRH.initial_gap_period_witness_limits (Q M : ℕ) (a H : ℝ) (hQ : 2<Q) (ha : a ≤ 1)
    (gap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime Q)
    (test : (Q.totient:ℝ)/4*(1+Real.sqrt (1+(H/a)^2)) < ((M:ℝ)+1)^a) :
    M ≤ 6 ∧ Q.totient ≤ 13 ∧ ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ 5 := by sorry
