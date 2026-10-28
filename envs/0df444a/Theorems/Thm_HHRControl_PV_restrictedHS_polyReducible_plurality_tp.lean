-- Prove2me | Theorems.Thm_HHRControl_PV_restrictedHS_polyReducible_plurality_tp
-- name    : HHRControl.PV.restrictedHS_polyReducible_plurality_tp
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:01:31.34192+00:00
-- url     : https://prove2.me/theorems/f375cbb8-b186-433f-83d2-c10e03659795
-- title:
--   Corollary 4.42 (Reduction) — Polynomial-time reduction from Restricted Hitting Set to voter-partition control for plurality in model TP
-- statement:
--   Restricted Hitting Set (`restrictedHSLang`) is polynomial-time many-one reducible both to constructive control by partition of voters (`ccLang .TP plurality`) and to destructive control by partition of voters (`dcLang .TP plurality`) for plurality voting in the Ties-Promote ($\mathrm{TP}$) model:
--   $$\mathrm{restrictedHSLang} \le_p \mathrm{ccLang}(\mathrm{TP}, \mathrm{plurality}) \;\wedge\; \mathrm{restrictedHSLang} \le_p \mathrm{dcLang}(\mathrm{TP}, \mathrm{plurality}).$$
--   Given a Restricted Hitting Set instance $(B, S, k)$ with $|B| = m$, $|S| = n$, $1 \le k$, and $n(k+1) + 1 \le m - k$, Construction 4.28 produces in polynomial time a plurality election over candidate set $C = B \cup \{c, w\}$ such that, by Claim 4.41, $S$ has a hitting set of size at most $k$ if and only if $w$ can be made the unique plurality winner in model $\mathrm{TP}$ by partitioning the voters, which holds if and only if $c$ can be prevented from being the unique plurality winner in model $\mathrm{TP}$ by partitioning the voters.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171(5–6):255–285 (arXiv:cs/0507027v5), pp. 24–28, Construction 4.28, Claim 4.41, and Corollary 4.42

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

set_option autoImplicit false

namespace HHRControl.PV

open CookPvsNP

theorem restrictedHS_polyReducible_plurality_tp :
    PolyReducible restrictedHSLang (ccLang .TP plurality) ∧
      PolyReducible restrictedHSLang (dcLang .TP plurality) := by sorry

end HHRControl.PV
