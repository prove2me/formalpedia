-- Prove2me | Theorems.Thm_Kyprianou_Ch04_discountedBVResidualIdentity
-- name    : Kyprianou.Ch04.discountedBVResidualIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:50:24.667239+00:00
-- url     : https://prove2.me/theorems/31de3131-b0fb-57b3-bbc3-eb718a15173e
-- title:
--   discountedBVResidualIdentity
-- statement:
--   Discounted bounded-variation change of variables minus physical compensation.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open Kyprianou.Ch04
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discounted bounded-variation change of variables minus physical compensation. -/
theorem Kyprianou.Ch04.discountedBVResidualIdentity {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (T : LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : ℝ), charFun (P.map (X t)) theta =
      Complex.exp (((t:ℝ):ℂ)*Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧
      (∫⁻ x in Ioo (-1:ℝ) 1, ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hLeft : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hXm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (l : ℝ)
    (G : ℝ → ℝ) (hG : G = fun y => ∫ x, (f (y+x)-f y) ∂T.levyMeasure)
    (hGc : Continuous G) :
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    let J := fun (t : NNReal) w => Real.exp (-l*(t:ℝ))*f (X t w)
    let k := fun (s x : ℝ) w => Real.exp (-l*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
    ∀ᵐ w ∂P, ∀ t : NNReal,
      (∫ s in Icc (0:ℝ) (t:ℝ), Real.exp (-l*s) *
        (d * deriv f (X s.toNNReal w)+G (X s.toNNReal w)-l*f (X s.toNNReal w)) ∂volume)
      = J t w-J 0 w -
        ((∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ univ, k z.1 z.2 w ∂(pathJumpMeasure X L w)) -
          ∫ s in Icc (0:ℝ) (t:ℝ), ∫ x, k s x w ∂T.levyMeasure ∂volume) := by
  sorry
