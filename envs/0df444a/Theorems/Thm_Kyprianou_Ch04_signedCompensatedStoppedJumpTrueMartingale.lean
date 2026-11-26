-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedCompensatedStoppedJumpTrueMartingale
-- name    : Kyprianou.Ch04.signedCompensatedStoppedJumpTrueMartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:27:43.292914+00:00
-- url     : https://prove2.me/theorems/c32dcc7e-0f7c-4668-82dd-c85f2f5d982b
-- title:
--   signedCompensatedStoppedJumpTrueMartingale
-- statement:
--   Signed Poisson compensation at a closed stopping clock is a true martingale under finite expected absolute stopped mass.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter Set LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed physical Poisson compensation at a closed stopping clock is a true martingale under finite stopped absolute mass. -/
theorem Kyprianou.Ch04.signedCompensatedStoppedJumpTrueMartingale {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (ha : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => k (t : ℝ) z.2 z.1))
    (hc : ∀ᵐ w ∂P, ∀ (x : ℝ) (t : NNReal), 0 < t →
      Tendsto (fun s : ℝ => k s x w) (nhdsWithin (t : ℝ) (Set.Iio (t : ℝ)))
        (nhds (k (t : ℝ) x w)))
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (n : ℕ) (w : Omega),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets nu n) ≠ ⊤)
    (hKernelPast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × (ℝ × ℝ) =>
        if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0))
    (hFin : ∀ t : NNReal, (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then k s x w else 0|
        ∂nu ∂volume ∂P) < ⊤) :
    let c := fun w (t : NNReal) => (min (tau w) (t : WithTop NNReal)).untopD t
    Martingale (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (c w t : ℝ) ×ˢ Set.univ, k z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (c w t : ℝ), ∫ x, k s x w ∂nu ∂volume) F P  := by
  sorry
