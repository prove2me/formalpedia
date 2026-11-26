-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise43StateExitResidualMartingales
-- name    : Kyprianou.Ch04.exercise43StateExitResidualMartingales
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:58:28.200348+00:00
-- url     : https://prove2.me/theorems/82b910ce-7f46-536d-8aed-e999db6ebe5c
-- title:
--   Exercise 4.3(iii): spatially stopped generator residual martingales
-- statement:
--   Under the corrected Exercise 4.3 physical and local domination hypotheses, the discounted generator residual integrated up to each spatial exit is a true martingale.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii), p. 107.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise43StateExitResidualMartingales
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal, Measurable[(F t)] (fun w : Ω => X t w))
    (T : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta = Complex.exp (((t : ℝ) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hNonLattice : T.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : ℝ, 0 < a ∧ T.levyMeasure
          {x : ℝ | ∃ k : Int, x = (k : ℝ) * a} =
        T.levyMeasure Set.univ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (lam : ℝ) (hlambda : 0 ≤ lam)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (w : Ω) => Real.exp (-lam * (t : ℝ)) * f (X t w)) F P)
    (hIntegrable : ∀ y : ℝ,
      Integrable (fun x : ℝ => f (y + x) - f y)
        T.levyMeasure)
    (L : NNReal → Ω → ℝ) (hLeft : ∀ᵐ w : Ω ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Set.Iio t)) (nhds (L t w)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P T.levyMeasure)
          (hJumpLaw : ∀ᵐ w : Ω ∂P, N.N w = pathJumpMeasure X L w)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b T.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂T.levyMeasure, ‖f (z+x)-f z‖ ≤ b x)
    (hLmeas : Measurable (fun z : ℝ × Ω => L z.1.toNNReal z.2))
    (hLadapted : ∀ t : NNReal, Measurable[F t] (L t))
    (hLpast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Ω × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ) then L z.2.toNNReal z.1 else 0))
    (hFuture : IsFutureIndependentPoissonMeasure P T.levyMeasure F N)
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ → Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (j : ℕ) (w : Ω),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets T.levyMeasure j) ≠ ⊤)
    (hXm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w))
    :
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    let G := fun y : ℝ => ∫ x, (f (y+x)-f y) ∂T.levyMeasure
    let H := fun y => d*deriv f y+G y-lam*f y
    let g := fun (r : ℝ) w => Real.exp (-lam*r)*H (X r.toNNReal w)
    let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    ∀ n, Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0:ℝ) (t:ℝ),
        (if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0) ∂volume) F P := by
  sorry
