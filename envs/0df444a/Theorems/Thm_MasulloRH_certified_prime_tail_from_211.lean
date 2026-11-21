-- Prove2me | Theorems.Thm_MasulloRH_certified_prime_tail_from_211
-- name    : MasulloRH.certified_prime_tail_from_211
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:04:04.792716+00:00
-- url     : https://prove2.me/theorems/2b50fd51-577e-4f79-a08f-fded366795dc
-- title:
--   A certified lower bound for the prime tail from 211 through 3200
-- statement:
--   A finite set of primes in the interval from 211 through 3200 contributes at least 0.000175 to the difference of the von Mangoldt series at 5/2 and 3.
-- source:
--   Extends marozols's verified cutoff 100 (https://prove2.me/theorems/a8a451bb-a157-45c1-b11e-fc5fd005e5b9, proof b660f3c2-41a3-42ae-913b-22f39ed737e2) using a sharper reference-mass bound and a new fixed-point certificate over primes from 211 to 3200.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet
open ArithmeticFunction MasulloRH

theorem MasulloRH.certified_prime_tail_from_211 : ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 211 ≤ p ∧ p ≤ 3200) ∧
      175000/1000000000 ≤ ∑ p ∈ P,
        (vonMangoldt p/(p:ℝ)^(5/2:ℝ) - vonMangoldt p/(p:ℝ)^(3:ℝ)) := by sorry
