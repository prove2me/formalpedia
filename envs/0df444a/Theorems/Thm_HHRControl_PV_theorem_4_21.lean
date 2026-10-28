-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_21
-- name    : HHRControl.PV.theorem_4_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:24.722858+00:00
-- url     : https://prove2.me/theorems/f131f903-0227-4b86-a2bd-0d2d76dc4d8b
-- title:
--   Theorem 4.21, p. 19 — approval is vulnerable/certifiably-vulnerable to destructive control by partition of voters in models TE and TP
-- statement:
--   **Theorem 4.21.** Approval voting is vulnerable and certifiably-vulnerable to destructive control by partition of voters, in model TE and in model TP.
--
--   That is, for each model: approval voting is susceptible to this control; the language of instances $(C,c,V)$ for which some partition of $V$ makes $c$ not the unique winner of the two-stage approval election is decidable in polynomial time; and a successful partition can be computed in polynomial time, with the answer "control impossible" on no-instances. (The paper's argument for model TP is the corrected one of Appendix A.)
--
--   It gives the two approval destructive clauses of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: solvable in polynomial time; the actual partition produced in polynomial time → the language of instance codes over BSym is in CookPvsNP.P; a CookPvsNP.PolyTimeComputable map sends the code of every yes-instance to the code of a successful partition and the code of every no-instance to a fixed token; reason: Definition 3.1 on Cook's one-tape machine; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 19, Theorem 4.21 (TP proof corrected in Appendix A, pp. 34–36)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.21, p. 19 (proof for TP in Appendix A, pp. 34–36): approval voting is
vulnerable/certifiably-vulnerable to destructive control by partition of voters in models TE and
TP. -/
theorem theorem_4_21 :
    (VulnerableDC .TE approval ∧ CertVulnerableDC .TE approval) ∧
      (VulnerableDC .TP approval ∧ CertVulnerableDC .TP approval) := by sorry

end HHRControl.PV
