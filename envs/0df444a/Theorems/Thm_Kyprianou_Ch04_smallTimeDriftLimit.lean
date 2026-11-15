-- Prove2me | Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
-- name    : Kyprianou.Ch04.smallTimeDriftLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:26:27.68172+00:00
-- url     : https://prove2.me/theorems/d10db7e8-3f1e-481c-9d98-851e5be5c7ce
-- title:
--   Lemma 4.11: almost-sure small-time bounded-variation drift limit
-- statement:
--   For any spectrally negative bounded-variation Levy process, with its genuine finite-variation drift d of arbitrary sign, P-almost every path satisfies lim_(t downarrow 0) X_t/t=d. The conclusion uses the right neighbourhood filter at zero and the Levy triplet's drift, not the mean drift psi'(0+).
-- source:
--   Kyprianou (2006), first edition, Lemma 4.11, printed page 102.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Lemma 4.11 (p. 102): the right-hand almost-sure small-time drift limit. -/
theorem smallTimeDriftLimit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    (∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => L.X t omega / (t : Real))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0))
        (nhds L.drift)) := by
  sorry
end Kyprianou.Ch04
