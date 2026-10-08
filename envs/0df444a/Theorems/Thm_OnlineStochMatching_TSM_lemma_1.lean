-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_lemma_1
-- name    : OnlineStochMatching.TSM.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:49:24.748985+00:00
-- url     : https://prove2.me/theorems/79272ee9-0567-4392-a956-b15ac6d3c7f6
-- title:
--   Lemma 1 — $|E_\delta| \le \frac23|A_{BR}| + \frac43|A_{BB}| + |A_B| + \frac13|A_R|$
-- statement:
--   Let $G = (A, I, E)$ be a finite bipartite graph, $E_f$ the edge set of an integral maximum flow of the boosted flow graph, blue/red a TSM colouring of $E_f$, and $E_\delta$ the set of edges crossing the surgered cut $(S, T)$ of Section 4.2.3 from $A \cap S$ to $I \cap T$. Then
--   $$|E_\delta| \;\le\; \tfrac23|A_{BR}| + \tfrac43|A_{BB}| + |A_B| + \tfrac13|A_R|.$$
--
--   The lemma relates the cut used to bound OPT to the two matchings that guide the algorithm. Substituted into equation (4), it bounds OPT by a linear form in $|A_{BR}|, |A_{BB}|, |A_B|, |A_R|$ that can be compared coefficient by coefficient with the lower bound (2) on ALG.
--
--   **Formalization Note** The inequality is stated over the reals. It is deterministic: it holds for every maximum flow edge set and every TSM colouring.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 8, Lemma 1 (proof pp. 8–9)

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Cut

namespace OnlineStochMatching.TSM

/-- **Lemma 1** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.3, p. 8; proof pp. 8–9): for a maximum flow edge set `E_f`, a TSM
colouring `(blue, red)` of it, and the cut edge set `E_δ` of §4.2.3,
`|E_δ| ≤ (2/3)|A_BR| + (4/3)|A_BB| + |A_B| + (1/3)|A_R|`. -/
theorem lemma_1 {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E F blue red : Finset (A × I)) (hF : IsMaxFlowSet E F) (hcol : IsTSMColoring F blue red) :
    ((Edelta E F).card : ℝ) ≤
      2 / 3 * (adsBR blue red).card + 4 / 3 * (adsBB blue red).card + (adsB blue red).card
        + 1 / 3 * (adsR blue red).card := by sorry

end OnlineStochMatching.TSM
