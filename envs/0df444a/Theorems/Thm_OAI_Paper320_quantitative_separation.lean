-- Prove2me | Theorems.Thm_OAI_Paper320_quantitative_separation
-- name    : OAI.Paper320.quantitative_separation
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.367315+00:00
-- url     : https://prove2.me/theorems/8d7692f3-0a27-4381-9a3f-20e7abf5d972
-- statement:
--   The theorem states that for every natural number d ≥ 1 there exist a positive integer n and a Boolean function f on the n-dimensional Boolean cube {false,true}ⁿ such that f maps the all-false input to false, f is not constant (some inputs x and y have f(x) ≠ f(y)), and the real inequality 2^d / (4(d+2)²) ≤ bs(f) / s(f)² holds. Here flipping a set B of coordinates of x negates exactly those coordinates. The sensitivity at x, sensitivityAt, counts the coordinates i for which flipping i alone changes f(x), and s(f) is the maximum of this count over all inputs. The block sensitivity at x is the largest number of pairwise disjoint nonempty coordinate sets B such that flipping B in x changes the value of f, and bs(f) is the maximum of this over all inputs. The ratio is taken in the reals, with the Lean convention that division by zero gives zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SensitivitySeparation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SensitivitySeparation.lean; bytes 927..1262
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SensitivitySeparation

namespace OAI

noncomputable section

open scoped Classical

namespace Paper320

theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  sorry

end Paper320
end
end OAI
