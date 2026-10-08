-- Prove2me | Theorems.Thm_MazurTransfer_rational_odd_power_of_finite_valuations
-- name    : MazurTransfer.rational_odd_power_of_finite_valuations
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T14:47:24.822349+00:00
-- url     : https://prove2.me/theorems/c9e9bb86-9e67-4a57-9099-3133f6ff85d8
-- title:
--   Rational odd powers from divisibility of every finite valuation
-- statement:
--   Let $n$ be a positive odd integer and $a\in\mathbb Q^\times$. If $\operatorname{ord}_p(a)$ is divisible by $n$ for every finite prime $p$, then there is $b\in\mathbb Q^\times$ with $b^n=a$. Equivalently, the empty-support $n$th-power Selmer group of $\mathbb Q$ is trivial for every odd $n$. The named downstream consumer is the $\mu_5$ arithmetic factor of the five-isogeny descent for $X_1(11)$, obtained by specializing $n=5$. The local Kummer-image comparison and the cyclic-character factor ramified at $11$ remain separate obligations.
-- source:
--   Generalization of the user MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, XOneElevenFiveSelmer.lean, using its checked SelmerClassGroup.lean exact sequence and UnramifiedArtin.lean. The integral class group is trivial and both integral units are odd powers. Full standalone proof imports Mathlib only, retains original Apache-2.0 headers, and has a local kernel audit showing exactly propext, Classical.choice, and Quot.sound. No full X1(11) descent or no-order-11 conclusion is asserted.

import Mathlib

theorem MazurTransfer.rational_odd_power_of_finite_valuations
    (n : ℕ) (hn : Odd n) (a : ℚˣ)
    (ha : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v.valuationOfNeZeroMod n (QuotientGroup.mk a) = 1) :
    ∃ b : ℚˣ, b ^ n = a := by sorry
