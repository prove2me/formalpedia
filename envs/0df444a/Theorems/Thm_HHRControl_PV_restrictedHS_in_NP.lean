-- Prove2me | Theorems.Thm_HHRControl_PV_restrictedHS_in_NP
-- name    : HHRControl.PV.restrictedHS_in_NP
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:01:36.356524+00:00
-- url     : https://prove2.me/theorems/8889653b-98e3-44b4-83e9-ecc18536adad
-- title:
--   Theorem 4.39 (NP membership) — Restricted Hitting Set is in NP
-- statement:
--   The Restricted Hitting Set problem (`restrictedHSLang`) belongs to the complexity class $\mathrm{NP}$:
--   $$\mathrm{restrictedHSLang} \in \mathrm{NP}.$$
--   An instance $(B, S, k)$ with $|B| = m$, $|S| = n$, $1 \le k$, and $n(k+1) + 1 + k \le m$ is a yes-instance if and only if there exists a subset $B' \subseteq B$ with $|B'| \le k$ that intersects every set $S_i$, which can be verified in polynomial time given the characteristic vector of $B'$.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171(5–6):255–285 (arXiv:cs/0507027v5), p. 27, Theorem 4.39

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

set_option autoImplicit false

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity

theorem restrictedHS_in_NP : restrictedHSLang ∈ NP BSym := by sorry

end HHRControl.PV
