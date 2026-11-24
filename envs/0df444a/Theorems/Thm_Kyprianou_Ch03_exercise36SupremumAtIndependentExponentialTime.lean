-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise36SupremumAtIndependentExponentialTime
-- name    : Kyprianou.Ch03.exercise36SupremumAtIndependentExponentialTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:52:13.620767+00:00
-- url     : https://prove2.me/theorems/a4ebd23e-785e-49d1-bcb9-ebd6fb1a5b55
-- title:
--   Exercise 3.6: exponential-horizon supremum and infinite-horizon limits
-- statement:
--   All three parts: memoryless factorisation of the supremum tail at an independent exponential time, its Exp(Phi(q)) law and the existence of nonnegative exponential moments, plus the infinite-horizon exponential or infinite supremum distribution.
-- source:
--   Kyprianou (2006), Exercise 3.6(i)-(iii), pp. 84-85; solution pp. 315-316.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise36SupremumAtIndependentExponentialTime
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    ∃ phi : ℝ, 0 < phi ∧ L.ψ phi = q ∧
      (∀ x y : ℝ, 0 < x → 0 < y →
        let tail (z : ℝ) :=
          ((P.prod Q) {pair : Omega × OmegaE |
             z < LevyExtrema.SBA.runSup
               (fun s => L.X s pair.1) (e pair.2)}).toReal
        tail (x + y) = tail x * tail y) ∧
      (∀ x : ℝ, 0 ≤ x →
        ((P.prod Q) {pair : Omega × OmegaE |
          x < LevyExtrema.SBA.runSup
            (fun s => L.X s pair.1) (e pair.2)}).toReal =
        Real.exp (-phi * x)) ∧
      (∀ beta : ℝ, 0 ≤ beta →
        ∀ t : NNReal, Integrable
          (fun omega => Real.exp (beta * L.X t omega)) P) ∧
      (∃ phi0 : ℝ, 0 ≤ phi0 ∧ L.ψ phi0 = 0 ∧
        (∀ theta : ℝ, 0 ≤ theta →
          L.ψ theta = 0 → theta ≤ phi0) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {omega : Omega |
            ∃ t : NNReal, x < L.X t omega}).toReal =
          Real.exp (-phi0 * x)) := by
  sorry

end Kyprianou.Ch03
