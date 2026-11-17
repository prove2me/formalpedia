-- Prove2me | Theorems.Thm_ManolescuPiccirillo_lee_d_squared
-- name    : ManolescuPiccirillo.lee_d_squared
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T18:53:52.121197+00:00
-- url     : https://prove2.me/theorems/d26e072d-d061-46ab-9a7e-bd3c452ef056
-- title:
--   The Lee differential squares to zero
-- statement:
--   For every diagram $D$ and homological degree $i$, the Lee differential satisfies $d_{i+1}\circ d_i=0$. This makes the Lee chain groups a genuine chain complex, so that the quotient $\ker d_0/\operatorname{im} d_{-1}$ defining $H^0_{\mathrm{Lee}}$ is its homology.
-- source:
--   Lee, An endomorphism of the Khovanov invariant, Adv. Math. 197 (2005) 554–586, https://arxiv.org/abs/math/0210213

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Movie
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_ManolescuPiccirillo_Lee2

namespace ManolescuPiccirillo
theorem lee_d_squared (D : PD) (i : ℤ) : (D.d (i + 1)).comp (D.d i) = 0 := by sorry
end ManolescuPiccirillo
