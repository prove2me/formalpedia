-- Prove2me | Theorems.Thm_Kyprianou_Ch02_emptyMarkPRMExistsV3
-- name    : Kyprianou.Ch02.emptyMarkPRMExistsV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:14:10.89334+00:00
-- url     : https://prove2.me/theorems/f41d412a-016d-46e1-bf95-aef36c0955d3
-- title:
--   Generic PRM existence for an empty measurable mark type
-- statement:
--   On an uninhabited measurable space every measurable subset is empty and any intensity is zero. Construct a zero counting measure on a singleton probability space, establish the degenerate Poisson(0) law and mutual independence of constant evaluations. This is the precise genuinely distinct empty-space case needed to specialise LeanLevy's inhabited Poisson point-family construction to arbitrary E.
-- source:
--   Kyprianou (2006) Chapter 2 original theorem 2.4; source-faithful decomposition of V3 canonical UUID 608b5f9b-92ff-404c-84cf-b60b94d76971; LeanLevy Poisson point-family existence and construction.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem emptyMarkPRMExistsV3
    (E : Type) [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    (hempty : ¬ Nonempty E) :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          (∀ (A : Set E), MeasurableSet A →
            Measurable (fun ω => N ω A)) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            P.map (fun ω => N ω A) =
              (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) ∧
          (∀ (A : Set E), MeasurableSet A → m A = ⊤ →
            ∀ᵐ ω ∂P, N ω A = ⊤) ∧
          (∀ {ι : Type} [Countable ι] (A : ι → Set E),
            (∀ i, MeasurableSet (A i)) →
            Pairwise (fun i j => Disjoint (A i) (A j)) →
            ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P) := by sorry
end Kyprianou.Ch02
