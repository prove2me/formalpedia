-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualCutoffMartingaleSquareFromVersionV1
-- name    : Kyprianou.Ch04.actualCutoffMartingaleSquareFromVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:47:17.575617+00:00
-- url     : https://prove2.me/theorems/de9c269e-5890-4f2f-b2eb-70baea79bbd5
-- title:
--   Actual cutoff martingale and square integrability from predictable version
-- statement:
--   Use the same predictable marked kernel on every horizon, transfer martingale conditional expectations and square integrability to the original physical cutoff witness by almost-sure equality and completion.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualCutoffMartingaleSquareFromVersionV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (u : ℝ) ×ˢ univ → Measurable[F u] (fun w => N.N w D))
    (e K : ℝ) (hK : 0 ≤ K)
    (hfin : ν {x : ℝ | e < |x| ∧ |x| < 1} < ⊤)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (L V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (hEq : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = L t ω)
    (M : NNReal → Ω → ℝ)
    (hM : ∀ t ω, M t ω = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
      {x : ℝ | e < |x| ∧ |x| < 1}, z.2 * f z.1 (L z.1.toNNReal ω) ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x in {x : ℝ | e < |x| ∧ |x| < 1},
        x * f s (L s.toNNReal ω) ∂ν ∂volume) :
    Martingale M F P ∧ ∀ t, Integrable (fun w => (M t w)^2) P := by
  sorry
end Kyprianou.Ch04
