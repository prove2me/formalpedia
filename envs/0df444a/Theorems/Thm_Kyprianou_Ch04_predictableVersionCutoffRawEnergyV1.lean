-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableVersionCutoffRawEnergyV1
-- name    : Kyprianou.Ch04.predictableVersionCutoffRawEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:31:05.782867+00:00
-- url     : https://prove2.me/theorems/c554ff1b-7030-42d1-b88b-77511f468ccf
-- title:
--   Physical cutoff energy using predictable versions of supplied left limits
-- statement:
--   For bounded continuous time-state weights, if each supplied cutoff left-limit process has a predictable version on a common full-measure event at every positive time, the terminal physical compensated cutoff differences satisfy the exact energy bound.
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
theorem predictableVersionCutoffRawEnergyV1 :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
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
    (XepsLeft V : ℝ → NNReal → Omega → ℝ)
    (hV : ∀ e : ℝ, 0 < e → e < 1 → IsStronglyPredictable F (V e))
    (hEq : ∀ e : ℝ, 0 < e → e < 1 →
      ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V e t ω = XepsLeft e t ω),
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
