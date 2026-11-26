-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedKernelPositiveParts
-- name    : Kyprianou.Ch04.signedKernelPositiveParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:11:28.8028+00:00
-- url     : https://prove2.me/theorems/ee309db3-fff8-45fa-afb8-fbdbd6b6bf55
-- title:
--   signedKernelPositiveParts
-- statement:
--   Positive and negative parts of a jointly measurable adapted signed marked kernel with common-null left continuity satisfy nonnegative admissibility and the same left-continuity condition.
-- source:
--   Kyprianou (2006), Exercise 4.3(i)-(ii), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Taking the positive and negative parts preserves marked kernel admissibility. -/
theorem Kyprianou.Ch04.signedKernelPositiveParts {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w))) :
    let kp := fun s x w => max (k s x w) 0
    let kn := fun s x w => max (-k s x w) 0
    IsAdmissiblePoissonKernel P F kp ∧ IsAdmissiblePoissonKernel P F kn ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => kp s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (kp (t : ℝ) x w))) ∧
    (∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => kn s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (kn (t : ℝ) x w))) := by
  sorry
