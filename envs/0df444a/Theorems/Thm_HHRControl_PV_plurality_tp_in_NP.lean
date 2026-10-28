-- Prove2me | Theorems.Thm_HHRControl_PV_plurality_tp_in_NP
-- name    : HHRControl.PV.plurality_tp_in_NP
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:01:59.363228+00:00
-- url     : https://prove2.me/theorems/4e19e29a-3241-46f6-bc17-8ba8533e5e07
-- title:
--   Corollary 4.42 (NP membership) — Constructive and destructive control by partition of voters for plurality in model TP are in NP
-- statement:
--   For plurality voting in the Ties-Promote ($\mathrm{TP}$) tie-handling model, both the constructive control by partition of voters language (`ccLang .TP plurality`) and the destructive control by partition of voters language (`dcLang .TP plurality`) belong to the complexity class $\mathrm{NP}$:
--   $$\mathrm{ccLang}(\mathrm{TP}, \mathrm{plurality}) \in \mathrm{NP} \;\wedge\; \mathrm{dcLang}(\mathrm{TP}, \mathrm{plurality}) \in \mathrm{NP}.$$
--   Given an encoded election instance $(C, c, V)$ and a partition $(V_1, V_2)$ of the voter set $V$ as a polynomial-length certificate, one can compute in polynomial time the plurality winners of the subelections $(C, V_1)$ and $(C, V_2)$, promote all winners of both subelections to the second-stage runoff with the full voter set $V$, and check whether $c$ is (or is not) the unique plurality winner of the resulting two-stage election.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171(5–6):255–285 (arXiv:cs/0507027v5), p. 28, Corollary 4.42

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

set_option autoImplicit false

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity

theorem plurality_tp_in_NP :
    ccLang .TP plurality ∈ NP BSym ∧ dcLang .TP plurality ∈ NP BSym := by sorry

end HHRControl.PV
