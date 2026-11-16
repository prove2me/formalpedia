-- Prove2me | Theorems.Thm_Kyprianou_poissonRandomMeasureExistsGenericCh02V3
-- name    : Kyprianou.poissonRandomMeasureExistsGenericCh02V3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T19:20:48.901196+00:00
-- url     : https://prove2.me/theorems/608b5f9b-92ff-404c-84cf-b60b94d76971
-- title:
--   Theorem 2.4: existence of a Poisson random measure on a sigma-finite space
-- statement:
--   Construct a random counting measure on any sigma-finite measurable space, including the zero or empty case, with Poisson counts of the correct finite intensity, infinite counts where the intensity is infinite, countable independent scattering and sample-wise countable additivity supplied by its Measure-valued representation.
-- source:
--   Kyprianou (2006), Theorem 2.4, pp. 39-40

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou

theorem poissonRandomMeasureExistsGenericCh02V3
    (E : Type) [MeasurableSpace E] (m : Measure E) [SigmaFinite m] :
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
            ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P)
      := by sorry

end Kyprianou
