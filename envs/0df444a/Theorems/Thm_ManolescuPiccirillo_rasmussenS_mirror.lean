-- Prove2me | Theorems.Thm_ManolescuPiccirillo_rasmussenS_mirror
-- name    : ManolescuPiccirillo.rasmussenS_mirror
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:55:51.56719+00:00
-- url     : https://prove2.me/theorems/c6c6d832-ca95-400a-9b5e-dbff5fdcad92
-- title:
--   $s$ of the mirror is $-s$
-- statement:
--   Taking the mirror of a knot diagram negates the Rasmussen invariant: $s(\overline{D})=-s(D)$.
-- source:
--   Rasmussen, Khovanov homology and the slice genus, Invent. Math. 182 (2010) 419–447, https://doi.org/10.1007/s00222-010-0275-6

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem rasmussenS_mirror (D : PD) (hD : D.IsKnot) (hN : D.NormalForm) :
    D.mirror.rasmussenS = -D.rasmussenS := by sorry
end ManolescuPiccirillo
