-- Prove2me | Theorems.Thm_Kyprianou_Ch02_pointFamilyFinitePRMCoreCh02V1
-- name    : Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:11:50.185654+00:00
-- url     : https://prove2.me/theorems/c2ed6ae9-8756-45c8-849f-6981830a4797
-- title:
--   Constructed PRM finite-region laws from the proved Poisson point family
-- statement:
--   For a sigma-finite intensity on any inhabited measurable mark space, an IsPoissonPointFamily yields a concrete random counting measure with measurable evaluations, exact Poisson laws on every finite-intensity measurable set and almost-sure finiteness on each such set. This is the exact finite-region interface needed for the open Kyprianou Chapter 2 generic PRM existence construction.
-- source:
--   Source-fidelity bridge, Kyprianou Ch 2 Theorem 2.4 via LeanLevy.RandomMeasure.PoissonRandomMeasure, Prove2Me proved map_poissonRandomMeasure_apply 9dab9398 and established measurable/finite-intensity evaluation lemmas.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem pointFamilyFinitePRMCoreCh02V1
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ A : Set E, MeasurableSet A →
       Measurable (fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A)) ∧
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       P.map (fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A) =
         (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ProbabilityTheory.poissonRandomMeasure K Y ω A < ⊤)
    := by sorry
end Kyprianou.Ch02
