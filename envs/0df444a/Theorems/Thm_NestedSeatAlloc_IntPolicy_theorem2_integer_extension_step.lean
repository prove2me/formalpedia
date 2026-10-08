-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_integer_extension_step
-- name    : NestedSeatAlloc.IntPolicy.theorem2_integer_extension_step
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T06:31:11.710113+00:00
-- url     : https://prove2.me/theorems/67f2fe78-70a6-482c-916e-a39cac96e5d5
-- title:
--   Theorem 2 induction step — integer extension from CLBI
-- statement:
--   Under the nested seat model, if the expected revenue through nest k is CLBI and the finite-prefix subdifferential condition holds through k, then an integer protection level exists at nest k+1 satisfying the next subdifferential condition.
-- source:
--   Brumelle & McGill (1993), Theorem 2 proof, Eqs. (27)–(30), p. 132

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_integer_extension_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (k : ℕ) (p : ℕ → ℕ)
    (hM : IsSeatModel P X f) (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i) (hk : 1 ≤ k)
    (hclbi : IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) k))
    (h20 : ∀ j, 1 ≤ j → j ≤ k →
      InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))) :
    ∃ n : ℕ, InSubdiff (expRevenue P X f (fun j => (p j : ℝ)) (k + 1)) n (f (k + 2)) := by sorry

end NestedSeatAlloc.IntPolicy
