-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_integrable_truncated_payoff_of_isSeatModel
-- name    : NestedSeatAlloc.IntPolicy.integrable_truncated_payoff_of_isSeatModel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T15:24:16.949664+00:00
-- url     : https://prove2.me/theorems/49efec90-5672-4da4-b8ed-b874af37e710
-- title:
--   Integrability of the nonnegative truncated one-class payoff
-- statement:
--   In a finite probability seat model, integer-valued nonnegative demand and a nonnegative coefficient make the truncated payoff integrable at every nonnegative seat level.
-- source:
--   Source-faithful bounded-integrability bridge in candidates/eq27_isSeatModel_truncated_integrable.lean; required by the equation-(27) CLBI and derivative constructions.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem integrable_truncated_payoff_of_isSeatModel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    {k : ℕ} {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    Integrable (fun ω => a * min s (X k ω)) P := by sorry

end NestedSeatAlloc.IntPolicy
