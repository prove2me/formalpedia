-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_19
-- name    : HHRControl.PV.theorem_4_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:37.964767+00:00
-- url     : https://prove2.me/theorems/764bcc1e-dd76-407b-9930-4304c80d07a8
-- title:
--   Theorem 4.19, p. 17 — in model TE, plurality is vulnerable/certifiably-vulnerable to destructive control by partition of voters
-- statement:
--   **Theorem 4.19.** In model TE, plurality voting is vulnerable and certifiably-vulnerable to destructive control by partition of voters.
--
--   That is: plurality is susceptible to this control; the language of instances $(C,c,V)$ for which some partition of $V$ makes $c$ not the unique winner of the TE two-stage election is decidable in polynomial time; and a successful partition can be computed in polynomial time, with the answer "control impossible" on no-instances.
--
--   It is the plurality destructive TE clause of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: solvable in polynomial time; the actual partition produced in polynomial time → the language of instance codes over BSym is in CookPvsNP.P; a CookPvsNP.PolyTimeComputable map sends the code of every yes-instance to the code of a successful partition and the code of every no-instance to a fixed token; reason: Definition 3.1 on Cook's one-tape machine; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 17, Theorem 4.19

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.19, p. 17: in model TE, plurality voting is vulnerable/certifiably-vulnerable to
destructive control by partition of voters. -/
theorem theorem_4_19 : VulnerableDC .TE plurality ∧ CertVulnerableDC .TE plurality := by sorry

end HHRControl.PV
