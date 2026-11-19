-- Prove2me | Theorems.Thm_ManolescuPiccirillo_rasmussenS_unknot
-- name    : ManolescuPiccirillo.rasmussenS_unknot
-- status  : Proved
-- author  : @LG
-- created : 2026-11-16T18:54:33.087144+00:00
-- url     : https://prove2.me/theorems/fbe8bd60-3260-4191-a64b-49409fac9863
-- title:
--   $s$ of the unknot is $0$
-- statement:
--   The Rasmussen $s$-invariant of the crossingless unknot diagram is $0$. This normalizes $s$ and is the base case of its slice-genus bound.
-- source:
--   Rasmussen, Khovanov homology and the slice genus, Invent. Math. 182 (2010) 419–447, https://doi.org/10.1007/s00222-010-0275-6

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem rasmussenS_unknot : (⟨[]⟩ : PD).rasmussenS = 0 := by sorry
end ManolescuPiccirillo
