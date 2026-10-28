-- Prove2me | Theorems.Thm_HHRControl_PV_corollary_4_42
-- name    : HHRControl.PV.corollary_4_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:08.071977+00:00
-- url     : https://prove2.me/theorems/1e501b22-0255-4961-9c30-b9daffa4cf1a
-- title:
--   Corollary 4.42, p. 28 — plurality is resistant to constructive and destructive control by partition of voters in model TP
-- statement:
--   **Corollary 4.42.**
--   1. Plurality voting is resistant to constructive control by partition of voters in model TP.
--   2. Plurality voting is resistant to destructive control by partition of voters in model TP.
--
--   Resistant means (Definition 3.1): susceptible to the control, and the language of yes-instances is NP-complete. The statement is made relative to the NP-completeness of Hitting Set (Garey and Johnson), which the paper cites. It gives the two plurality TP clauses of Theorem 3.6.
--
--   Differences from the source:
--   - reading: Hitting Set is NP-complete, see Garey and Johnson [GJ79] (cited, p. 23) → hypothesis hHS : NPComplete hittingSetLang; reason: the paper imports this fact without proof and the platform has no proof of it; precedent GTWSched.NPC.theorem_1, MultiPurchase.Hardness.theorem_1
--   - encoding: NP-complete (Definition 3.1, footnote 7) → CookPvsNP.NPComplete of the language of instance codes over BSym (membership in Cook's NP and a polynomial-time many-one reduction from every NP language); reason: Cook's one-tape machine model; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 28, Corollary 4.42

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Corollary 4.42, p. 28: plurality voting is resistant to constructive and to destructive control
by partition of voters in model TP (given the NP-completeness of Hitting Set, [GJ79]). -/
theorem corollary_4_42 (hHS : NPComplete hittingSetLang) :
    ResistantCC .TP plurality ∧ ResistantDC .TP plurality := by sorry

end HHRControl.PV
