-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorComplexLaplaceFromTripletV1
-- name    : Kyprianou.Ch02.subordinatorComplexLaplaceFromTripletV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:19:00.391956+00:00
-- url     : https://prove2.me/theorems/6a5e9f26-6f8b-4442-9a7b-7bdc8867318e
-- title:
--   Complex Laplace transform of a subordinator from its characteristic triplet
-- statement:
--   For a nonnegative-valued Lévy process with the stated characteristic triplet and subordinator constraints, the complex Laplace transform on the closed right half-plane is the exponential of the drift-plus-uncompensated-jump exponent. The transform is derived from the characteristic law, not assumed.
-- source:
--   Kyprianou (2006), Lemma 2.15 and proof of (2.27); isolates the missing complex Laplace identity after Lemma 2.14 gives the subordinator triplet constraints. The existing independentSubordinationCh02 then supplies the independent time-change conclusion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorComplexLaplaceFromTripletV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (τ : ℝ≥0 → Ω → ℝ≥0)
    (aτ : ℝ) (στ : ℝ≥0) (ντ : Measure ℝ)
    (hντ : ProbabilityTheory.IsLevyMeasure ντ)
    (hτ : ProbabilityTheory.IsLevyProcess
       (fun t ω => (τ t ω : ℝ)) P)
    (hτchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => (τ t ω : ℝ))) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-aτ, στ ^ 2, ντ, hντ⟩ ξ))
    (hneg : ντ (Set.Iio (0 : ℝ)) = 0)
    (hsigma : στ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ντ.restrict (Set.Ioi (0 : ℝ))))
    (hdis : 0 ≤ -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ) :
    let d : ℝ := -aτ - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ντ
    let Ξ : ℂ → ℂ := fun z =>
      (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ),
        (1 - Complex.exp (-z * ((x : ℝ) : ℂ))) ∂ντ
    ∀ (t : ℝ≥0) (z : ℂ), 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (((τ t ω : ℝ) : ℂ))) ∂P =
        Complex.exp (-(((t : ℝ) : ℂ)) * Ξ z) := by sorry
