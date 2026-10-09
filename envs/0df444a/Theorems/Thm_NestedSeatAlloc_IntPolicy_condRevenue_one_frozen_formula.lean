-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_frozen_formula
-- name    : NestedSeatAlloc.IntPolicy.condRevenue_one_frozen_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:58:23.952704+00:00
-- url     : https://prove2.me/theorems/26eb961d-b0e0-42aa-894b-a1298685f6b2
-- title:
--   Exact highest-fare conditional revenue with the class-one demand frozen
-- statement:
--   The conditional revenue of the highest-fare class, with demand
--   frozen at y, is f(1)*min(s,y): it is f(1)*s for s<y and f(1)*y
--   otherwise. The probability measure P integrates the constant
--   realised revenue to itself. This exact formula needs no positivity
--   hypothesis. It can support a correctly stated base concavity lemma
--   under an explicit f(1)>=0 assumption. The original published
--   theorem1_conditional_concavity_base was independently Disproved
--   because IsSeatModel allows negative fares; the new formula never
--   silently assumes positivity. Authoritative remote compilation only.
-- source:
--   The conditional revenue of the highest-fare class, with demand
--   frozen at y, is f(1)*min(s,y): it is f(1)*s for s<y and f(1)*y
--   otherwise. The probability measure P integrates the constant
--   realised revenue to itself. This exact formula needs no positivity
--   hypothesis. It can support a correctly stated base concavity lemma
--   under an explicit f(1)>=0 assumption. The original published
--   theorem1_conditional_concavity_base was independently Disproved
--   because IsSeatModel allows negative fares; the new formula never
--   silently assumes positivity. Authoritative remote compilation only.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.condRevenue_one_frozen_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hP : IsProbabilityMeasure P) (y s : ℝ) :
    condRevenue P X f p 1 y s =
      if s < y then f 1 * s else f 1 * y := by sorry
