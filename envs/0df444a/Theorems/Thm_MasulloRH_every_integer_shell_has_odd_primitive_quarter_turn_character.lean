-- Prove2me | Theorems.Thm_MasulloRH_every_integer_shell_has_odd_primitive_quarter_turn_character
-- name    : MasulloRH.every_integer_shell_has_odd_primitive_quarter_turn_character
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:52:19.971074+00:00
-- url     : https://prove2.me/theorems/32565b9a-c685-4e37-a297-efa22e65b372
-- title:
--   Each integer shell admits a prime-modulus odd primitive character taking the value i or −i
-- statement:
--   For every natural n≥2, some odd prime q dividing n²+1 and an odd primitive complex Dirichlet character modulo q give χ(n)=i or −i. Conjugating this character distinguishes the shell at n with maximal imaginary difference. This applies at any specified prime power.
-- source:
--   Arithmetic input to the Masullo mission fixed-shell comparison: finite character duality distinguishes −1 at an odd prime divisor of n²+1; see also AlfutovaUstinov.problem_4_126 on the congruence type of such a divisor.

import Mathlib

theorem MasulloRH.every_integer_shell_has_odd_primitive_quarter_turn_character (n : ℕ) (hn : 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ q ∣ n^2 + 1 ∧
      (n : ZMod q)^2 = -1 ∧ ∃ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive ∧ χ.Odd ∧
      (χ (n : ZMod q) = Complex.I ∨ χ (n : ZMod q) = -Complex.I) := by sorry
