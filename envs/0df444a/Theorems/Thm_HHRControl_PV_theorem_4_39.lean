-- Prove2me | Theorems.Thm_HHRControl_PV_theorem_4_39
-- name    : HHRControl.PV.theorem_4_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:51.457276+00:00
-- url     : https://prove2.me/theorems/856b47b4-9e36-401e-9c89-443abcd3dd73
-- title:
--   Theorem 4.39, p. 27 — Restricted Hitting Set is NP-complete
-- statement:
--   **Restricted Hitting Set** asks, for a set $B=\{b_1,\dots,b_m\}$, a family $S=\{S_1,\dots,S_n\}$ of subsets of $B$ and a positive integer $k$ with
--   $$n(k+1)+1\le m-k,$$
--   whether $S$ has a hitting set of size at most $k$, i.e. a set $B'\subseteq B$ with $\|B'\|\le k$ and $S_i\cap B'\neq\emptyset$ for each $i$.
--
--   **Theorem 4.39.** Restricted Hitting Set is NP-complete.
--
--   The statement is made relative to the NP-completeness of the unrestricted Hitting Set problem (Garey and Johnson), which the paper cites. Restricted Hitting Set is the source problem of the reduction in Claim 4.41.
--
--   Differences from the source:
--   - reading: Hitting Set is NP-complete, see Garey and Johnson [GJ79] (cited, p. 23) → hypothesis hHS : NPComplete hittingSetLang; reason: the paper imports this fact without proof and the platform has no proof of it; precedent GTWSched.NPC.theorem_1, MultiPurchase.Hardness.theorem_1
--   - encoding: n(k + 1) + 1 ≤ m − k → n * (k + 1) + 1 + k ≤ m; reason: avoids natural-number subtraction; the two inequalities have the same solutions (the left side is ≥ 1)
--   - encoding: NP-complete (Definition 3.1, footnote 7) → CookPvsNP.NPComplete restrictedHSLang, the language of the binary codes hsCode (m, n, k, incidence rows of the Sᵢ) of the yes-instances; reason: Cook's one-tape machine model; the incidence-row code has length polynomial in the size of (B, S, k)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 27, Restricted Hitting Set and Theorem 4.39; Hitting Set p. 24

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages

namespace HHRControl.PV

open CookPvsNP

/-- Theorem 4.39, p. 27: Restricted Hitting Set is NP-complete (given the NP-completeness of
Hitting Set, Garey–Johnson [GJ79], cited on p. 23). -/
theorem theorem_4_39 (hHS : NPComplete hittingSetLang) : NPComplete restrictedHSLang := by sorry

end HHRControl.PV
