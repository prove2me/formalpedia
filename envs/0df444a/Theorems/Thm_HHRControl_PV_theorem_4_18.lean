-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_18
-- name    : HHRControl.PV.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:43.51899+00:00
-- url     : https://prove2.me/theorems/dea13256-162f-4a89-b115-8f4db9a3c291
-- title:
--   Theorem 4.18, p. 15 — in model TE, plurality is vulnerable/certifiably-vulnerable to constructive control by partition of voters
-- statement:
--   **Theorem 4.18.** In model TE, plurality voting is vulnerable and certifiably-vulnerable to constructive control by partition of voters.
--
--   That is: plurality is susceptible to this control (some election has a candidate $c$, not the unique winner, whom some partition makes the unique two-stage winner); the language of yes-instances $(C,c,V)$ — those with a partition of $V$ into $V_1,V_2$ making $c$ the unique winner when, under TE, each subcommittee nominates its unique plurality winner (nobody on a tie) and the nominees run against each other with voter set $V$ — is decidable in polynomial time; and a successful partition can be computed in polynomial time, with the answer "control impossible" on no-instances.
--
--   It is the plurality constructive TE clause of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: solvable in polynomial time; the actual partition produced in polynomial time → the language of instance codes over BSym is in CookPvsNP.P; a CookPvsNP.PolyTimeComputable map sends the code of every yes-instance to the code of a successful partition and the code of every no-instance to a fixed token; reason: Definition 3.1 on Cook's one-tape machine; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 15, Theorem 4.18

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.18, p. 15: in model TE, plurality voting is vulnerable/certifiably-vulnerable to
constructive control by partition of voters. -/
theorem theorem_4_18 : VulnerableCC .TE plurality ∧ CertVulnerableCC .TE plurality := by sorry

end HHRControl.PV
