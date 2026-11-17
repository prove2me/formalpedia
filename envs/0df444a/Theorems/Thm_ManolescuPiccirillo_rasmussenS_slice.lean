-- Prove2me | Theorems.Thm_ManolescuPiccirillo_rasmussenS_slice
-- name    : ManolescuPiccirillo.rasmussenS_slice
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:57:38.792084+00:00
-- url     : https://prove2.me/theorems/162227c4-3aaa-482e-9fae-74e14d59388d
-- title:
--   Slice knots have $s=0$
-- statement:
--   If a knot diagram $D$ admits a slice-disk movie (so the knot is smoothly slice), then $s(D)=0$. This is Rasmussen's slice obstruction, the contrapositive of which certifies non-sliceness from $s\ne 0$; it is the property that makes the Manolescu–Piccirillo strategy work.
-- source:
--   Rasmussen, Khovanov homology and the slice genus, Invent. Math. 182 (2010) 419–447, https://doi.org/10.1007/s00222-010-0275-6

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem rasmussenS_slice (D : PD) (hD : D.IsKnot) (hN : D.NormalForm)
    (h : HasSliceMovie D) : D.rasmussenS = 0 := by sorry
end ManolescuPiccirillo
