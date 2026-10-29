-- Prove2me | Theorems.Thm_HHRControl_PV_approval_cc_in_NP
-- name    : HHRControl.PV.approval_cc_in_NP
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-27T06:01:36.637149+00:00
-- url     : https://prove2.me/theorems/327816ca-30ae-4c9c-b0ab-c485cad4252b
-- title:
--   Theorems 4.45 & 4.46 (NP membership) — Constructive control by partition of voters for approval voting is in NP
-- statement:
--   For approval voting under either tie-handling rule $\mathrm{rule} \in \{\mathrm{TE}, \mathrm{TP}\}$, the constructive control by partition of voters language (`ccLang rule approval`) belongs to $\mathrm{NP}$:
--   $$\forall \mathrm{rule} \in \{\mathrm{TE}, \mathrm{TP}\},\quad \mathrm{ccLang}(\mathrm{rule}, \mathrm{approval}) \in \mathrm{NP}.$$
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, Artificial Intelligence 171(5–6):255–285 (arXiv:cs/0507027v5), pp. 29–30, Theorems 4.45 and 4.46

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

set_option autoImplicit false

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity

theorem approval_cc_in_NP (rule : TieRule) :
    ccLang rule approval ∈ NP BSym := by sorry

end HHRControl.PV
