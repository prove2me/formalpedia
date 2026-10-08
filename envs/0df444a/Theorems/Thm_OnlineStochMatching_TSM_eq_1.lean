-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_eq_1
-- name    : OnlineStochMatching.TSM.eq_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:35:00.894001+00:00
-- url     : https://prove2.me/theorems/38157cac-a616-4c14-8cc7-d10b86c8f9c2
-- title:
--   Equation (1) — $|E_f| = 2|A_{BR}| + 2|A_{BB}| + |A_B| + |A_R|$
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph, $E_f$ the edge set of an integral maximum flow of the boosted flow graph, and blue/red a TSM colouring of $E_f$. Write $A_{BR}$, $A_{BB}$, $A_B$, $A_R$ for the advertisers incident to one blue and one red edge, to two blue edges, to only a blue edge, and to only a red edge. Then
--   $$|E_f| = 2|A_{BR}| + 2|A_{BB}| + |A_B| + |A_R|.$$
--
--   The identity says that every edge of $E_f$ is counted at its advertiser, and that no advertiser carries two red edges. It converts the bound on OPT, which is in terms of $|E_f|$, into the advertiser classes in which ALG is bounded.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 7, Section 4.2.2, equation (1)

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring

namespace OnlineStochMatching.TSM

/-- **Equation (1)** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.2, p. 7): for a maximum flow edge set `E_f` and a TSM colouring
`(blue, red)` of it,
`|E_f| = 2|A_BR| + 2|A_BB| + |A_B| + |A_R|`,
where `A_BR`, `A_BB`, `A_B`, `A_R` are the advertisers incident to one blue and one red edge, to
two blue edges, to only a blue edge, and to only a red edge. -/
theorem eq_1 {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red) :
    F.card = 2 * (adsBR blue red).card + 2 * (adsBB blue red).card + (adsB blue red).card +
      (adsR blue red).card := by sorry

end OnlineStochMatching.TSM
