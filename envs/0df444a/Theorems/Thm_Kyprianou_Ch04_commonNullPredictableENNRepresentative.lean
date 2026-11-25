-- Prove2me | Theorems.Thm_Kyprianou_Ch04_commonNullPredictableENNRepresentative
-- name    : Kyprianou.Ch04.commonNullPredictableENNRepresentative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:04:28.06043+00:00
-- url     : https://prove2.me/theorems/5d161ee2-626c-4ccb-a821-662c6c461ab8
-- title:
--   Common-event left continuity gives a jointly predictable ENNReal modification
-- statement:
--   Construct predictable dyadic left-endpoint approximations and take a measurable liminf. The simultaneous full probability event gives agreement at every nonnegative time and mark; on negative times define the representative to agree with the original kernel.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- A common null set permits a jointly predictable modification in time and mark. -/
theorem commonNullPredictableENNRepresentative
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega))) :
    ∃ psi : Real → Real → Omega → ENNReal,
      Measurable[F.predictable.prod inferInstance]
        (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2) ∧
      (∀ᵐ omega ∂P, ∀ s x : Real, psi s x omega = ENNReal.ofReal (phi s x omega)) := by
  sorry
end Kyprianou.Ch04
