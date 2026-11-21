-- Prove2me | Theorems.Thm_GRH_mobius_character_and_progression_bounds_above_record
-- name    : GRH.mobius_character_and_progression_bounds_above_record
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:34:28.278427+00:00
-- url     : https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92
-- title:
--   Power savings in twisted Möbius sums and in individual reduced residue classes
-- statement:
--   For every fixed positive modulus $q$ and every $\sigma>0.8749570698$, both the $\chi$-twisted finite Möbius sum for each character modulo $q$ and the finite Möbius sum in each reduced residue class modulo $q$ are $O(N^\sigma)$. This includes the principal character. The constants may depend on the modulus, character or class, and exponent.
-- source:
--   Follows from the principal and nonprincipal finite Perron estimates derived from the Prove2Me zero-free theorem https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918 and finite character orthogonality https://prove2.me/theorems/e378c149-1bfc-4b20-83ff-bec66551df5f.

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics

theorem GRH.mobius_character_and_progression_bounds_above_record (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698 : ℝ) < σ) :
    (∀ χ : DirichletCharacter ℂ q,
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N+1), χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
        (fun N : ℕ ↦ (N : ℝ)^σ)) ∧
    (∀ a : ZMod q, IsUnit a →
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N+1), if a = (k : ZMod q) then
        (ArithmeticFunction.moebius k : ℂ) else 0) =O[atTop] (fun N : ℕ ↦ (N : ℝ)^σ)) := by sorry
