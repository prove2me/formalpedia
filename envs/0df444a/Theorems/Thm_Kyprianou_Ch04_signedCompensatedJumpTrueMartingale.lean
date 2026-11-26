-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedCompensatedJumpTrueMartingale
-- name    : Kyprianou.Ch04.signedCompensatedJumpTrueMartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:17:49.641666+00:00
-- url     : https://prove2.me/theorems/4e37d594-47cf-4045-8a8f-f53fb43e7895
-- title:
--   signedCompensatedJumpTrueMartingale
-- statement:
--   The signed compensated physical Poisson integral is a true martingale under finite expected absolute mass, joint past measurability, common-null left continuity and adapted locally finite Poisson evaluations.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Signed physical Poisson compensation is a true martingale under finite absolute mass. -/
theorem Kyprianou.Ch04.signedCompensatedJumpTrueMartingale {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
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
      ∫⁻ x, ENNReal.ofReal |k s x w| ∂nu ∂volume ∂P) < ⊤) :
    Martingale (fun (t : NNReal) w =>
      (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ, k z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, k s x w ∂nu ∂volume) F P := by
  sorry
