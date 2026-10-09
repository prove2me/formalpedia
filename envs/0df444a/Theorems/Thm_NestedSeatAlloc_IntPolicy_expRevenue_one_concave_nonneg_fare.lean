-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_concave_nonneg_fare
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_one_concave_nonneg_fare
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:39:47.367868+00:00
-- url     : https://prove2.me/theorems/34a51392-bb73-446d-aee2-aa1e33f511a2
-- title:
--   First-class expected revenue is concave with nonnegative first fare
-- statement:
--   For any seat model with nonnegative first fare, the expected
--   revenue of the highest-fare class is concave on nonnegative seats.
--
--   The proof uses the published conditional frozen-revenue formula and
--   its new nonnegative-fare concavity lemma, then the Proved
--   concaveOn_of_ae_integral_representation.
--   Revenue integrability is supplied by the already Proved
--   revenue_integrable_of_seat_model at nest 1.
--
--   This repairs the missing positivity hypothesis in the disproved
--   unrestricted first-class conditional-concavity base. It also
--   provides the class-one concavity premise for the already published
--   theorem1_of_first_class_concavity. The exact original Theorem 1
--   still requires showing nonnegative f 1 from its stated assumptions,
--   or another valid base argument. No local Lean/Lake run.
-- source:
--   For any seat model with nonnegative first fare, the expected
--   revenue of the highest-fare class is concave on nonnegative seats.
--
--   The proof uses the published conditional frozen-revenue formula and
--   its new nonnegative-fare concavity lemma, then the Proved
--   concaveOn_of_ae_integral_representation.
--   Revenue integrability is supplied by the already Proved
--   revenue_integrable_of_seat_model at nest 1.
--
--   This repairs the missing positivity hypothesis in the disproved
--   unrestricted first-class conditional-concavity base. It also
--   provides the class-one concavity premise for the already published
--   theorem1_of_first_class_concavity. The exact original Theorem 1
--   still requires showing nonnegative f 1 from its stated assumptions,
--   or another valid base argument. No local Lean/Lake run.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.expRevenue_one_concave_nonneg_fare {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hf1 : 0 ≤ f 1) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1) := by sorry
