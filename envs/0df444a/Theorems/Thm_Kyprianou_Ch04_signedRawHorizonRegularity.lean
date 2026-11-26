-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedRawHorizonRegularity
-- name    : Kyprianou.Ch04.signedRawHorizonRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:17:53.117384+00:00
-- url     : https://prove2.me/theorems/9f054f6b-64b7-432f-b9f4-22276d3560ef
-- title:
--   signedRawHorizonRegularity
-- statement:
--   The signed raw Poisson integral is exactly adapted and agrees almost surely with the difference of its positive and negative parts.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Raw signed Poisson integration has exact adaptedness and a.e. signed-part splitting. -/
theorem Kyprianou.Ch04.signedRawHorizonRegularity {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (t : NNReal)
    (hPast : ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ n : ℕ, ∀ w : Omega,
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets nu n) ≠ ⊤)
    (hP : IsAdmissiblePoissonKernel P F (fun s x w => max (k s x w) 0))
    (hN : IsAdmissiblePoissonKernel P F (fun s x w => max (-k s x w) 0))
    (hcP : ∀ᵐ w ∂P, ∀ (x : ℝ) (u : NNReal), 0 < u →
      Tendsto (fun s : ℝ => max (k s x w) 0) (nhdsWithin (u : ℝ) (Set.Iio (u : ℝ)))
        (nhds (max (k (u : ℝ) x w) 0)))
    (hcN : ∀ᵐ w ∂P, ∀ (x : ℝ) (u : NNReal), 0 < u →
      Tendsto (fun s : ℝ => max (-k s x w) 0) (nhdsWithin (u : ℝ) (Set.Iio (u : ℝ)))
        (nhds (max (-k (u : ℝ) x w) 0)))
    (hmP : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (k z.2.1 z.2.2 z.1) 0 else 0))
    (hmN : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (-k z.2.1 z.2.2 z.1) 0 else 0))
    (hp : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (k s x w) 0) ∂nu ∂volume ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-k s x w) 0) ∂nu ∂volume ∂P) < ⊤) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    StronglyMeasurable[F t] (fun w => ∫ z in V, k z.1 z.2 w ∂(N.N w)) ∧
    ∀ᵐ w ∂P, (∫ z in V, k z.1 z.2 w ∂(N.N w)) =
      (∫ z in V, max (k z.1 z.2 w) 0 ∂(N.N w)) -
      ∫ z in V, max (-k z.1 z.2 w) 0 ∂(N.N w) := by
  sorry
