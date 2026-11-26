-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingWitnessV2
-- name    : Kyprianou.Ch05.canonicalPositivePoissonCrossingWitnessV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:53:33.43726+00:00
-- url     : https://prove2.me/theorems/81e50e7b-ea5e-5bd2-8df9-9e324f9151dd
-- title:
--   Predictable crossing integrand and finite-horizon limits for the canonical positive Poisson path
-- statement:
--   Construct the predictable left-limit crossing integrand; identify its Poisson sum pathwise with the unique discounted crossing and its intensity integral with the occupation kernel, then take monotone limits. No expectation equality between these two sides is assumed.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.canonicalPositivePoissonCrossingWitnessV2
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (eta d : ℝ) (heta : 0 ≤ eta) (hdrift : 0 ≤ d)
    (hs : Pi (Iic (0 : ℝ)) = 0)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (H : (NNReal → ℝ) → ENNReal) (hHmeas : Measurable H)
    (hH : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0)     (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} Q Pi)
    (hN : ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ))
    (F : Filtration NNReal inferInstance)
    (hF : ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi)
      (Iic (t : ℝ) ×ˢ univ)) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∃ psi : ℝ → ℝ → Lambda → ENNReal,
      Measurable[F.predictable.prod inferInstance]
        (fun z : (NNReal × Lambda) × ℝ => psi (z.1.1 : ℝ) z.2 z.1.2) ∧
      Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (n : ℝ) ×ˢ univ,
        psi z.1 z.2 w ∂(N.N w) ∂Q) atTop (nhds (∫⁻ f, H f ∂(Q.map (fun w t => X t w)))) ∧
      Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        ∫⁻ z, psi t z w ∂Pi ∂volume ∂Q) atTop (nhds (
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
      (∫⁻ v, (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
          ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
        else 0) v ∂(Q.map (X (Real.toNNReal t)))) ∂volume)) := by
  sorry
