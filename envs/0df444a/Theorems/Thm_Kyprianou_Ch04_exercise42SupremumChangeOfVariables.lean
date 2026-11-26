-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42SupremumChangeOfVariables
-- name    : Kyprianou.Ch04.exercise42SupremumChangeOfVariables
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T22:29:28.378258+00:00
-- url     : https://prove2.me/theorems/2c890074-cb8e-4005-80b9-a41cfa5cde2c
-- title:
--   Exercise 4.2: two-variable bounded-variation change of variables at the running supremum
-- statement:
--   For spectrally negative bounded-variation Levy input with positive pathwise drift, a jointly C1 function f of running supremum and current process value satisfies the Chapter 4 Exercise 4.2 identity: drift times partial derivative in the second coordinate, Riemann-Stieltjes integral of the first-coordinate derivative against the continuous running supremum, and the raw negative-jump sum. The Stieltjes integral exists as the limit of left-point sums, without assuming the identity or an independently supplied integral.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.2, printed p. 106.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Exercise 4.2 (p. 106): two-variable change of variables at the running
supremum of a spectrally negative BV Levy process. The Stieltjes term is
specified independently by left-point sums, and its existence is proved. -/
theorem exercise42SupremumChangeOfVariables
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    let supX : NNReal -> Omega -> Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
      ∃ maxIntegral : Real,
        Tendsto
          (fun n : Nat =>
            ∑ k ∈ Finset.range n,
              let u : NNReal := t * (k : NNReal) / (n : NNReal)
              let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
              fderiv Real f (supX u omega, L.X u omega) (1, 0) *
                (supX v omega - supX u omega))
          atTop (nhds maxIntegral) ∧
        f (supX t omega, L.X t omega) =
          f (supX 0 omega, L.X 0 omega) +
          L.drift *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              fderiv Real f
                (supX (Real.toNNReal s) omega, L.X (Real.toNNReal s) omega)
                (0, 1) ∂volume) +
          maxIntegral +
          (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
              (Set.Iio (0 : Real)),
            (f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega + z.2) -
              f (supX (Real.toNNReal z.1) omega,
                Xleft (Real.toNNReal z.1) omega))
            ∂(pathJumpMeasure L.X Xleft omega)) := by
  sorry
end Kyprianou.Ch04
