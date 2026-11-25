-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedVariationChangeOfVariables
-- name    : Kyprianou.Ch04.boundedVariationChangeOfVariables
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:22:29.295676+00:00
-- url     : https://prove2.me/theorems/949a2995-9202-4880-8431-e7d57b0da724
-- title:
--   Theorem 4.2: full bounded-variation Levy change of variables
-- statement:
--   For any real-valued Levy process of bounded variation, with arbitrary positive and negative jumps and real finite-variation drift d=b-integral_{|x|<1}x nu(dx), and any C^(1,1) test function, the full time-space chain-rule equality holds almost surely: initial value, ordinary time derivative, d times spatial derivative, and raw path jump sum. The theorem is not restricted to spectrally negative processes. The characteristic exponent law ensures that the explicit Levy triplet is the triplet of the process.
-- source:
--   Kyprianou (2006), first edition, Theorem 4.2, printed page 91.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.2 (p. 91): change of variables for a general bounded-variation Levy process. -/
theorem boundedVariationChangeOfVariables
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (Xleft : NNReal → Omega → Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      0 < t →
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      f ((t : Real), X t omega) =
        f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (s, X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        (triplet.drift -
          ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            fderiv Real f (s, X (Real.toNNReal s) omega)
              (0, 1) ∂volume) +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega))
          ∂(pathJumpMeasure X Xleft omega)) := by
  sorry
end Kyprianou.Ch04
