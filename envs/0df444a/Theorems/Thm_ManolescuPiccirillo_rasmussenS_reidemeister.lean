-- Prove2me | Theorems.Thm_ManolescuPiccirillo_rasmussenS_reidemeister
-- name    : ManolescuPiccirillo.rasmussenS_reidemeister
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:56:47.465009+00:00
-- url     : https://prove2.me/theorems/acd9096a-997c-4f2d-934e-9a29b62784ce
-- title:
--   $s$ is a Reidemeister invariant
-- statement:
--   If two normal-form diagrams $D,D'$ are related by a sequence of Reidemeister moves, then $s(D)=s(D')$. Thus $s$ descends to a knot invariant.
-- source:
--   Rasmussen, Khovanov homology and the slice genus, Invent. Math. 182 (2010) 419–447, https://doi.org/10.1007/s00222-010-0275-6 ; Lee, An endomorphism of the Khovanov invariant, Adv. Math. 197 (2005) 554–586, https://arxiv.org/abs/math/0210213

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem rasmussenS_reidemeister (D D' : PD) (hN : D.NormalForm) (hN' : D'.NormalForm)
    (h : D.ReidemeisterEquiv D') : D.rasmussenS = D'.rasmussenS := by sorry
end ManolescuPiccirillo
