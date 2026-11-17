-- Prove2me | Theorems.Thm_ManolescuPiccirillo_sMax_sub_sMin
-- name    : ManolescuPiccirillo.sMax_sub_sMin
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:54:56.982729+00:00
-- url     : https://prove2.me/theorems/ba63b9a8-302d-4abf-b698-3cbd6e8d764a
-- title:
--   The two Lee filtration degrees differ by $2$
-- statement:
--   For a knot diagram $D$ in normal form, the maximal and minimal quantum-filtration degrees of non-zero classes in degree-zero Lee homology satisfy $s_{\max}(D)-s_{\min}(D)=2$. Consequently $s(D)=(s_{\max}+s_{\min})/2$ is an integer and $s_{\max}=s(D)+1$, $s_{\min}=s(D)-1$; this is the well-definedness of Rasmussen's invariant.
-- source:
--   Rasmussen, Khovanov homology and the slice genus, Invent. Math. 182 (2010) 419–447, https://doi.org/10.1007/s00222-010-0275-6

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem sMax_sub_sMin (D : PD) (hD : D.IsKnot) (hN : D.NormalForm) :
    D.sMax - D.sMin = 2 := by sorry
end ManolescuPiccirillo
