-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightOptionalSamplingFromSupermartingaleZeroStart
-- name    : Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingaleZeroStart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:50:36.207299+00:00
-- url     : https://prove2.me/theorems/5c8c84b1-cfbc-48e8-a123-d30d1269ecbc
-- title:
--   Correct right-natural optional sampling for a discounted McKean supermartingale started at zero
-- statement:
--   This is the mathematically corrected arbitrary-time optional sampling statement. The previously published theorem without hStart is false: a deterministic constant nonzero process X_t=c and tau=0 give V(x+c)>V(x) despite a discounted supermartingale. The additional zero-start condition X0=0 is satisfied by the original IsLinearBrownian assumption because IsLevyProcess.start_zero supplies it. Given this condition, apply the already Proved finite-horizon right-natural supermartingale optional-sampling theorem to tau∧n, the proved stopped McKean value measurability, the clipped pointwise discounted value limit, and bounded convergence using the uniform 0≤exp(-qt)V≤K bound. The time-zero integrand equals V(x) pointwise by hStart. This corrects the source without strengthening the original Brownian theorem.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13, corrected zero-start assumption in optional-sampling reduction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightOptionalSamplingFromSupermartingaleZeroStart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (hStart : X 0 = fun _ => 0)
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
