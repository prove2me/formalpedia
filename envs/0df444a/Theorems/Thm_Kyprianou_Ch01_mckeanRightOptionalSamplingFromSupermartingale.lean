-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightOptionalSamplingFromSupermartingale
-- name    : Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T17:14:39.442886+00:00
-- url     : https://prove2.me/theorems/1127c3e9-2c08-42f9-a97e-00612ca83dc1
-- title:
--   Right-natural optional sampling for a bounded discounted McKean supermartingale
-- statement:
--   Given the genuine discounted McKean supermartingale relative to the right-natural filtration, derive its optional-sampling inequality at an arbitrary possibly infinite right-natural stopping time. The value function is nonnegative and uniformly bounded by K, and discount exp(-qt) ensures convergence to zero at infinity. Apply the already Proved MarkovProcess continuous-time bounded supermartingale optional-stopping theorem to bounded truncations min(tau,n), then use stopped-path continuity and dominated convergence to pass to the original possibly infinite tau. Identify the initial value with the time-zero Brownian surplus and ensure Z is measurable and integrable. This is the second, abstract stochastic-analysis bridge from the Brownian supermartingale to the precise theorem expectation bound.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; arbitrary right-natural optional sampling and infinity convention.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t)
    (hSM : Supermartingale
      (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X t ω)) F P)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    let barrier := Real.log (K * phi / (1 + phi))
    let Z : Ω → ℝ := fun ω =>
      match tau ω with
      | none => 0
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)
    Integrable Z P ∧
      (∫ ω, Z ω ∂P) ≤ mckeanValue K barrier phi x := by sorry
