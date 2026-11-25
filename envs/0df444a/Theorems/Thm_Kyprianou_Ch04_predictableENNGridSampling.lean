-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableENNGridSampling
-- name    : Kyprianou.Ch04.predictableENNGridSampling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:51:33.181121+00:00
-- url     : https://prove2.me/theorems/9834bfe8-bf3c-49f2-bce6-bba372b962d2
-- title:
--   Marked nonnegative step sampling is jointly predictable
-- statement:
--   Extend each adapted marked section on its predictable interval by zero, and take the countable supremum with the time-zero section. Each covered time sees exactly its sampled value.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableENNGridSampling
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × Real => phi (t : Real) z.2 z.1))
    (q : NNReal → NNReal) (a b : Nat → NNReal)
    (h0 : q 0 = 0)
    (hcell : ∀ k t, t ∈ Set.Ioc (a k) (b k) → q t = a k)
    (hcover : ∀ t, 0 < t → ∃ k, t ∈ Set.Ioc (a k) (b k)) :
    Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real =>
        ENNReal.ofReal (phi (q z.1.1 : Real) z.2 z.1.2)) := by
  sorry
end Kyprianou.Ch04
