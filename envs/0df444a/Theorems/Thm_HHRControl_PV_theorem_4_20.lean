-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_20
-- name    : HHRControl.PV.theorem_4_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:27.49146+00:00
-- url     : https://prove2.me/theorems/75a27c5a-31d4-4f58-9c46-aabf2bf78c87
-- title:
--   Theorem 4.20, p. 18 — Condorcet is vulnerable/certifiably-vulnerable to destructive control by partition of voters
-- statement:
--   **Theorem 4.20.** Condorcet voting is vulnerable and certifiably-vulnerable to destructive control by partition of voters.
--
--   That is: Condorcet voting is susceptible to this control; the language of instances $(C,c,V)$ for which some partition of $V$ makes $c$ not the unique winner of the two-stage Condorcet election is decidable in polynomial time; and a successful partition can be computed in polynomial time, with the answer "control impossible" on no-instances. The statement holds for each tie-handling model; both give the same two-stage election, since a Condorcet winner, when it exists, is unique.
--
--   It is the Condorcet clause of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: solvable in polynomial time; the actual partition produced in polynomial time → the language of instance codes over BSym is in CookPvsNP.P; a CookPvsNP.PolyTimeComputable map sends the code of every yes-instance to the code of a successful partition and the code of every no-instance to a fixed token; reason: Definition 3.1 on Cook's one-tape machine; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
--   - encoding: Condorcet: the models TE and TP do not apply (p. 3) → stated for both tie rules; reason: a Condorcet winner is unique when it exists, so TE and TP nominate the same candidates and give the same two-stage election
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 18, Theorem 4.20

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.20, p. 18: Condorcet voting is vulnerable/certifiably-vulnerable to destructive
control by partition of voters (in either tie-handling model). -/
theorem theorem_4_20 (rule : TieRule) :
    VulnerableDC rule condorcet ∧ CertVulnerableDC rule condorcet := by sorry

end HHRControl.PV
