-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingIntensityLimitV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonCrossingIntensityLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:50:05.07259+00:00
-- url     : https://prove2.me/theorems/ac1fffa3-849f-5c0e-9e61-b29414b62d26
-- title:
--   Expected intensity integral converges to the discounted potential kernel
-- statement:
--   For each fixed positive time, the Poisson measure has no atom on that time slice. Thus the pre-jump value agrees almost surely with the current path value. Factor the discounted mark integral into the measurable potential kernel, use the marginal pushforward, Tonelli and monotone convergence of the integer horizons.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonCrossingIntensityLimitV1
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
      (Iic (t : ℝ) ×ˢ univ))
    (V : NNReal → Lambda → ℝ)
    (hV : Measurable[F.predictable] (Function.uncurry V))
    (hleft : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s => d * (s : ℝ) +
        (∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) t) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    let psi := fun (s z : ℝ) (w : Lambda) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        ∫⁻ z, psi t z w ∂Pi ∂volume ∂Q) atTop (nhds (
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
      (∫⁻ v, (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
          ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
        else 0) v ∂(Q.map (X (Real.toNNReal t)))) ∂volume)) := by
  sorry
