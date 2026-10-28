-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_3_6
-- name    : HHRControl.PV.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:24.026193+00:00
-- url     : https://prove2.me/theorems/bbcde1f1-5734-4766-8710-de90eb6841bd
-- title:
--   Theorem 3.6, p. 8 — control by partition of voters: approval, plurality and Condorcet, in models TE and TP
-- statement:
--   In **control by partition of voters** the chair splits the voters $V$ into two subcommittees $V_1,V_2$; each holds a subelection over all candidates $C$ and nominates its winners — all of them in model **TP** (Ties-Promote), only a unique winner in model **TE** (Ties-Eliminate) — and the nominees run against each other with voter set $V$. Constructive control asks for a partition making a given $c$ the unique winner, destructive control for one making $c$ not the unique winner.
--
--   **Theorem 3.6.**
--   1. Approval is resistant to constructive control by partition of voters in models TE and TP, and vulnerable/certifiably-vulnerable to destructive control by partition of voters in models TE and TP.
--   2. Plurality is vulnerable/certifiably-vulnerable to both constructive and destructive control by partition of voters in model TE, and is resistant to both constructive and destructive control by partition of voters in model TP.
--   3. Condorcet is vulnerable/certifiably-vulnerable to destructive control by partition of voters.
--
--   Here (Definition 3.1) *vulnerable* means susceptible and the language of yes-instances is in P; *certifiably-vulnerable* means susceptible and a successful partition (or "control impossible") is computable in polynomial time; *resistant* means susceptible and the language is NP-complete. The theorem is stated relative to the NP-completeness of Hitting Set and of Exact Cover by Three-Sets, the two facts the paper cites from Garey and Johnson.
--
--   The striking point is that plurality switches between vulnerable and resistant depending only on the tie-handling rule.
--
--   **Formalization Note** P, NP-completeness and polynomial-time computability are `CookPvsNP` notions on Cook's one-tape machine, applied to the languages of binary instance codes over `BSym`. The nine clauses are a single conjunction in the order of the statement; the Condorcet clause is stated for both tie rules.
--
--   Differences from the source:
--   - reading: Hitting Set is NP-complete, see Garey and Johnson [GJ79] (cited, p. 23) → hypothesis hHS : NPComplete hittingSetLang; reason: the paper imports this fact without proof and the platform has no proof of it; precedent GTWSched.NPC.theorem_1, MultiPurchase.Hardness.theorem_1
--   - reading: X3C is NP-complete, see Garey and Johnson [GJ79] (cited, p. 28) → hypothesis hX3C : NPComplete x3cLang; reason: the paper imports this fact without proof and the platform has no proof of it; same precedent
--   - encoding: solvable in polynomial time; the actual partition produced in polynomial time → the language of instance codes over BSym is in CookPvsNP.P; a CookPvsNP.PolyTimeComputable map sends the code of every yes-instance to the code of a successful partition and the code of every no-instance to a fixed token; reason: Definition 3.1 on Cook's one-tape machine; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
--   - encoding: NP-complete (Definition 3.1, footnote 7) → CookPvsNP.NPComplete of the language of instance codes over BSym (membership in Cook's NP and a polynomial-time many-one reduction from every NP language); reason: Cook's one-tape machine model; instances are coded ballot by ballot (p. 4), so the code length is polynomially related to the paper's input size
--   - encoding: Condorcet: the models TE and TP do not apply (p. 3) → stated for both tie rules; reason: a Condorcet winner is unique when it exists, so TE and TP nominate the same candidates and give the same two-stage election
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 8, Theorem 3.6

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 3.6, p. 8: approval is resistant to constructive control by partition of voters in
models TE and TP, and vulnerable/certifiably-vulnerable to destructive control by partition of voters
in models TE and TP. Plurality is vulnerable/certifiably-vulnerable to both constructive and
destructive control by partition of voters in model TE, and is resistant to both constructive and
destructive control by partition of voters in model TP. Condorcet is vulnerable/certifiably-vulnerable
to destructive control by partition of voters. The NP-completeness of Hitting Set and of X3C
(Garey–Johnson [GJ79], cited on pp. 23 and 28) are the hypotheses. -/
theorem theorem_3_6 (hHS : NPComplete hittingSetLang) (hX3C : NPComplete x3cLang) :
    -- approval, constructive: resistant in TE and TP
    ResistantCC .TE approval ∧ ResistantCC .TP approval ∧
    -- approval, destructive: vulnerable/certifiably-vulnerable in TE and TP
    (VulnerableDC .TE approval ∧ CertVulnerableDC .TE approval) ∧
    (VulnerableDC .TP approval ∧ CertVulnerableDC .TP approval) ∧
    -- plurality, TE: vulnerable/certifiably-vulnerable, constructive and destructive
    (VulnerableCC .TE plurality ∧ CertVulnerableCC .TE plurality) ∧
    (VulnerableDC .TE plurality ∧ CertVulnerableDC .TE plurality) ∧
    -- plurality, TP: resistant, constructive and destructive
    ResistantCC .TP plurality ∧ ResistantDC .TP plurality ∧
    -- Condorcet, destructive: vulnerable/certifiably-vulnerable (both models give the same election)
    ∀ rule : TieRule, VulnerableDC rule condorcet ∧ CertVulnerableDC rule condorcet := by sorry

end HHRControl.PV
