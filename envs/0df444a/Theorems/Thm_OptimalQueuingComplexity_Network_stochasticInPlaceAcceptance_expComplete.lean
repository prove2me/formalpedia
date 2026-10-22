-- Prove2me | Theorems.Thm_OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance_expComplete
-- name    : OptimalQueuingComplexity.Network.stochasticInPlaceAcceptance_expComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T10:28:31.482971+00:00
-- url     : https://prove2.me/theorems/567998c0-c527-4f8b-83c9-d4ac886ead98
-- title:
--   Lemma 1 — STOCHASTIC IN-PLACE ACCEPTANCE is EXP-complete
-- statement:
--   STOCHASTIC IN-PLACE ACCEPTANCE, with instances $(M, n)$ encoded as the machine's binary description followed by $n$ in unary, is EXP-complete:
--   $$\text{SIPA} \in \mathrm{EXP} \quad\text{and}\quad L \le_p \text{SIPA} \text{ for every language } L \in \mathrm{EXP}.$$
--
--   This is the reduction source for the hardness half of Theorem 1. It turns polynomial space for stochastic machines into exponential time.
--
--   **Formalization Note.** Acceptance is "some depth-$k$ tree value exceeds $1/2$", with leaving the input squares counted as rejection. This coincides with the paper's tree value on precise machines.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 296, Lemma 1

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Network_EXPComplete
import Definitions.Def_OptimalQueuingComplexity_Network_stochasticInPlaceAcceptance

namespace OptimalQueuingComplexity.Network

/-- Lemma 1 (Papadimitriou & Tsitsiklis 1999, p. 296): STOCHASTIC IN-PLACE ACCEPTANCE is
EXP-complete. -/
theorem stochasticInPlaceAcceptance_expComplete :
    EXPComplete SIPAInstance.enc stochasticInPlaceAcceptance := by sorry

end OptimalQueuingComplexity.Network
