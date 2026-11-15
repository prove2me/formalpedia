-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kellaWhittTrueMartingale
-- name    : Kyprianou.Ch04.kellaWhittTrueMartingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:25:00.180206+00:00
-- url     : https://prove2.me/theorems/8636720e-9247-4d94-9159-c207ad18e6b2
-- title:
--   Theorem 4.7: Kella-Whitt true martingale
-- statement:
--   For each alpha>=0, psi(alpha) times the time integral of exp(-alpha*(barX_s-X_s)) plus 1 minus exp(-alpha*(barX_t-X_t)) minus alpha*barX_t is a true P-martingale with respect to the filtration, under spectrally negative bounded-variation Levy input with positive linear drift. The statement does not weaken true martingale to local martingale.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.7, printed page 98.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.7 (p. 98): the full Kella-Whitt true martingale. -/
theorem kellaWhittTrueMartingale
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ alpha : Real, 0 ≤ alpha →
      let supX : NNReal → Omega → Real := fun t omega =>
        sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
      MeasureTheory.Martingale
        (fun (t : NNReal) omega =>
          L.ψ alpha *
            (∫ s in Set.Icc (0 : Real) (t : Real),
              Real.exp (-alpha * (supX (Real.toNNReal s) omega - L.X (Real.toNNReal s) omega))
                ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
            alpha * supX t omega) F P := by
  sorry
end Kyprianou.Ch04
