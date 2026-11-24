-- Prove2me | Theorems.Thm_Kyprianou_Ch03_submultiplicativeMomentsIffLargeJumpIntegral
-- name    : Kyprianou.Ch03.submultiplicativeMomentsIffLargeJumpIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:39:54.682516+00:00
-- url     : https://prove2.me/theorems/1a81fd8e-6331-4cbd-bab7-6061fab42164
-- title:
--   Theorem 3.8: submultiplicative moment criterion
-- statement:
--   A measurable nonnegative submultiplicative function bounded on compact subsets is integrable against the large-jump Levy measure precisely when it has a finite expectation at each strictly positive time.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.8, pp. 76-78.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem submultiplicativeMomentsIffLargeJumpIntegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (g : Real -> Real)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : forall R : Real, 0 <= R ->
      exists M : Real, forall x : Real, abs x <= R -> g x <= M) :
    (IntegrableOn g {x : Real | 1 <= abs x} T.levyMeasure) <->
    (forall (t : NNReal), 0 < t ->
      Integrable (fun omega => g (X t omega)) P) := by
  sorry

end Kyprianou.Ch03
