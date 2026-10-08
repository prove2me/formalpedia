-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_policy_assembly
-- name    : NestedSeatAlloc.IntPolicy.theorem2_policy_assembly
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-06T06:52:37.702066+00:00
-- url     : https://prove2.me/theorems/91910933-9911-474a-9a5b-3b064d0bea73
-- title:
--   Theorem 2 assembly — coherent finite prefixes yield one integer policy
-- statement:
--   If every admissible finite integer protection prefix can be extended by one level while preserving the finite subdifferential conditions, and the required CLBI hypotheses hold for such prefixes, then one infinite integer policy satisfies the subdifferential condition at every nest.
-- source:
--   Brumelle & McGill (1993), Theorem 2 proof, recursive choice of the integer protection vector from the base case and one-step covering induction, pp. 132–133.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_policy_assembly {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f)
    (hprefix : ∀ k (p : ℕ → ℕ), 1 ≤ k →
      (∀ j, 1 ≤ j → j ≤ k →
        InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))) →
      IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) k) →
      ∃ n : ℕ, ∀ j, 1 ≤ j → j ≤ k + 1 →
        InSubdiff (expRevenue P X f (fun i =>
          if i = k + 1 then (n : ℝ) else (p i : ℝ)) j)
          (if j = k + 1 then n else p j) (f (j + 1)))
    (hbase : ∃ n : ℕ,
      InSubdiff (expRevenue P X f (fun i => (n : ℝ)) 1) n (f 2)) :
    ∃ p : ℕ → ℕ, SubdiffCondition P X f (fun k => (p k : ℝ)) := by sorry

end NestedSeatAlloc.IntPolicy
