-- Prove2me | Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingPathLimitV1
-- name    : Kyprianou.Ch05.canonicalPositivePoissonCrossingPathLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:50:01.217294+00:00
-- url     : https://prove2.me/theorems/b2f533e0-3fe2-508a-b02e-f6198e8f88ac
-- title:
--   Expected marked Poisson crossing integral converges to the discounted crossing law
-- statement:
--   On a common full-measure set, positive Poisson arrivals have distinct times and the canonical cumulative path has their marks as its jumps. The predictable representative equals the left limit. Integrate the marked crossing indicator over all arrivals, identify its unique crossing summand with H, and use monotone convergence over integer time horizons.
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

theorem Kyprianou.Ch05.canonicalPositivePoissonCrossingPathLimitV1
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
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (n : ℝ) ×ˢ univ,
        psi z.1 z.2 w ∂(N.N w) ∂Q) atTop (nhds (∫⁻ f, H f ∂(Q.map (fun w t => X t w)))) := by
  sorry
