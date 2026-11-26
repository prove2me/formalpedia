-- Prove2me | Theorems.Thm_Kyprianou_Ch04_adaptedCutoffRawEnergyV1
-- name    : Kyprianou.Ch04.adaptedCutoffRawEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:08:45.668441+00:00
-- url     : https://prove2.me/theorems/798a4a55-fedb-4a05-851c-a7f5c81b1a5d
-- title:
--   Physical energy of two adapted cutoff integrals
-- statement:
--   For a jump measure with measurable past counts and independent future counts, the two bounded continuous spatial weights evaluated at strict left limits of adapted cutoff processes satisfy the stated terminal compensated Poisson energy inequality.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem adaptedCutoffRawEnergyV1 :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P triplet.levyMeasure F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (fSpace : ℝ → ℝ → ℝ)
    (hJoint : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (K : ℝ) (hK : 0 < K)
    (hBound : ∀ s x : ℝ, 0 ≤ s → |fSpace s x| ≤ K)
    (Xeps XepsLeft : ℝ → NNReal → Omega → ℝ)
    (hAdapt : ∀ e : ℝ, 0 < e → e < 1 → Adapted F (Xeps e))
    (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
      ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => Xeps epsilon s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (XepsLeft epsilon t omega))),
    ∀ (T : NNReal), 0 < T ->
          ∀ (M : Real -> NNReal -> Omega -> Real),
            (∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
              (∀ t omega, M epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
        {x : Real | epsilon < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
        ∂(N.N omega)) -
      (∫ s in Set.Icc (0 : Real) (t : Real),
        (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
          ∂triplet.levyMeasure) ∂volume)) ∧
              MeasureTheory.Martingale (M epsilon) F P) ->
    ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤
        (∫ ω, ∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft a s.toNNReal ω)) z -
            ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft b s.toNNReal ω)) z)^2
              ∂triplet.levyMeasure ∂volume ∂P) := by
  sorry
end Kyprianou.Ch04
