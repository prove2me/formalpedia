-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_46
-- name    : HHRControl.PV.theorem_4_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:53.440552+00:00
-- url     : https://prove2.me/theorems/4738a878-44db-420c-a115-bfc0e2896928
-- title:
--   Theorem 4.46, p. 30 — approval is resistant to constructive control by partition of voters in model TE
-- statement:
--   **Theorem 4.46.** Approval voting is resistant to constructive control by partition of voters in model TE.
--
--   That is, approval voting is susceptible to this control, and the language of instances $(C,c,V)$ for which some partition of $V$ makes $c$ the unique winner of the TE two-stage approval election is NP-complete. The statement is made relative to the NP-completeness of Exact Cover by Three-Sets (Garey and Johnson), which the paper cites. It is the approval constructive TE clause of Theorem 3.6.
--
--   Differences from the source:
--   - reading: X3C is NP-complete, see Garey and Johnson [GJ79] (cited, p. 28) → hypothesis hX3C : NPComplete x3cLang; reason: the paper imports this fact without proof and the platform has no proof of it; same precedent
--   - encoding: NP-complete (Definition 3.1, footnote 7) → CookPvsNP.NPComplete of the language of instance codes over BSym (membership in Cook's NP and a polynomial-time many-one reduction from every NP language); reason: Cook's one-tape machine model; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 30, Theorem 4.46; X3C p. 28

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.46, p. 30: approval voting is resistant to constructive control by partition of
voters in model TE (given the NP-completeness of X3C, [GJ79]). -/
theorem theorem_4_46 (hX3C : NPComplete x3cLang) : ResistantCC .TE approval := by sorry

end HHRControl.PV
