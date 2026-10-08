-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_eq_3
-- name    : OnlineStochMatching.TSM.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:49:08.395981+00:00
-- url     : https://prove2.me/theorems/c8ff7ff4-b07b-4df9-bf9e-a3da3405fcd4
-- title:
--   Equation (3) — $|E_f| = 2(|A_T| + |I_S|) + |E_\delta|$
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph, $E_f$ the edge set of an integral maximum flow of the boosted flow graph $G_f$, and $(S, T)$ the cut obtained from the residual reachability cut by moving to $S$ every impression type of $T$ joined to more than one advertiser of $S$. With $A_T = A \cap T$, $I_S = I \cap S$ and $E_\delta$ the set of edges of $E$ from $A \cap S$ to $I \cap T$,
--   $$|E_f| = 2\big(|A_T| + |I_S|\big) + |E_\delta|.$$
--
--   The identity is the max-flow min-cut theorem applied to this cut, whose capacity consists of the source arcs into $A_T$, the sink arcs out of $I_S$ (both of capacity 2) and the crossing edges $E_\delta$. It is combined with (1) to express the bound on OPT in the advertiser classes.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 8, Section 4.2.3, equation (3); the cut (S, T) is defined on p. 7

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Cut

namespace OnlineStochMatching.TSM

/-- **Equation (3)** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.3, p. 8): for a maximum flow edge set `E_f` of the boosted flow
graph `G_f` and the cut `(S, T)` obtained from the residual reachability cut by the surgery of
§4.2.3 (p. 7),
`|E_f| = 2(|A_T| + |I_S|) + |E_δ|`,
where `E_δ` is the set of edges of `E` from `A_S` to `I_T`. -/
theorem eq_3 {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F : Finset (A × I)) (hF : IsMaxFlowSet E F) :
    F.card = 2 * ((cutAT E F).card + (cutIS E F).card) + (Edelta E F).card := by sorry

end OnlineStochMatching.TSM
