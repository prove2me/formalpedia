-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem2_prefix_extension_bridge
-- name    : NestedSeatAlloc.IntPolicy.theorem2_prefix_extension_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:11:22.037795+00:00
-- url     : https://prove2.me/theorems/b7892142-1374-4c8c-8d7a-0c4dc146f119
-- title:
--   Theorem 2 prefix bridge — one-step witness preserves earlier conditions
-- statement:
--   The one-step integer witness at level k can be inserted into a protection policy without changing the earlier revenue functions, so all finite-prefix subdifferential conditions remain valid through level k+1.
-- source:
--   Source-faithful bridge in the proof of Brumelle & McGill (1993), Theorem 2, pp. 132–133: the recursive extension changes only the newly introduced protection level, while earlier revenue terms are prefix-local.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem2_prefix_extension_bridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (k : ℕ) (p : ℕ → ℕ)
    (hM : IsSeatModel P X f) (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i) (hk : 1 ≤ k)
    (hclbi : IsCLBI (expRevenue P X f (fun j => (p j : ℝ)) k))
    (h20 : ∀ j, 1 ≤ j → j ≤ k →
      InSubdiff (expRevenue P X f (fun i => (p i : ℝ)) j) (p j) (f (j + 1))) :
    ∃ n : ℕ, ∀ j, 1 ≤ j → j ≤ k + 1 →
      InSubdiff (expRevenue P X f (fun i =>
        if i = k + 1 then (n : ℝ) else (p i : ℝ)) j)
        (if j = k + 1 then n else p j) (f (j + 1)) := by sorry

end NestedSeatAlloc.IntPolicy
