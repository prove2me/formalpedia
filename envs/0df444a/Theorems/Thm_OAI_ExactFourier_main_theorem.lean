-- Prove2me | Theorems.Thm_OAI_ExactFourier_main_theorem
-- name    : OAI.ExactFourier.main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:39.363132+00:00
-- url     : https://prove2.me/theorems/1b39a049-4e3b-489c-bdd4-2ad9266f4e5c
-- statement:
--   The theorem states that the defined proposition MainStatement holds. Circuits here are scalar straight-line programs over the complex numbers on n inputs: starting from the n inputs and a constant zero, each charged gate adds two available values, subtracts two available values, or multiplies one available value by an arbitrary fixed complex constant, and earlier values are never consumed, so reuse and fanout are free. A circuit's n outputs each name any available value, so permutations and fanout are uncharged, and its size is the number of gates. A circuit computes a matrix A if, for every input vector x in ℂⁿ, its outputs equal A x. The Fourier matrix F_n has entries ζ_n^(jk) for j,k in {0,...,n−1}, where ζ_n = exp(2πi/n). MainStatement says that for every real c>0 and every integer N₀≥2 there exists n≥N₀ and a circuit on n inputs computing F_n exactly whose size is strictly less than c·n·log₂ n. Equivalently, along some infinite sequence of dimensions, exact scalar circuits for the discrete Fourier transform have size o(n log n); the formalization places no bound on the magnitude of the complex constants.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ExactFourier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ExactFourier.lean; bytes 1927..1977
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ExactFourier

namespace OAI

namespace ExactFourier

theorem main_theorem : MainStatement := by
  sorry

end ExactFourier
end OAI
