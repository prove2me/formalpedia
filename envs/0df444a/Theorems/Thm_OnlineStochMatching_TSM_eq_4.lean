-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_eq_4
-- name    : OnlineStochMatching.TSM.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:49:05.101569+00:00
-- url     : https://prove2.me/theorems/2b817a1d-4966-4415-b5b8-04c6d7d6ae0f
-- title:
--   Equation (4) — w.h.p. OPT $\le |A_{BR}| + |A_{BB}| + \frac12(|A_B|+|A_R|) + (\frac12 - \frac1e)|E_\delta| + \varepsilon n$
-- statement:
--   Consider the online stochastic matching problem with $e_i = 1$: a finite bipartite graph $G = (A, I, E)$, and $n = |I|$ arrivals whose types are drawn independently and uniformly from $I$. Let $E_f$ be the edge set of an integral maximum flow of the boosted flow graph, blue/red a TSM colouring of it, $E_\delta$ the crossing edge set of the surgered cut of Section 4.2.3, and $\mathrm{OPT}$ the size of a maximum matching of the realization graph.
--
--   For every $\varepsilon > 0$ there are $\delta > 0$ and $N$ such that, whenever $n \ge N$, for every such instance, $E_f$ and colouring, with probability at least $1 - e^{-\delta n}$,
--   $$\mathrm{OPT} \;\le\; |A_{BR}| + |A_{BB}| + \tfrac12\big(|A_B| + |A_R|\big) + \Big(\tfrac12 - \tfrac1e\Big)|E_\delta| + \varepsilon n.$$
--
--   Together with Lemma 1 and equation (2) this gives the approximation ratio of Theorem 5.
--
--   **Formalization Note** The paper's "with probability $1 - e^{-\Omega(n)}$" is made explicit: $\delta$ and $N$ depend on $\varepsilon$ only and are chosen before the instance. The $O(1)$ term of the intermediate bound $|A^*_\delta| \le (1 - 1/e)|E_\delta| + \varepsilon n + O(1)$ on p. 8 is absorbed into $\varepsilon n$ for $n \ge N$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 8, Section 4.2.3, equation (4)

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Cut

namespace OnlineStochMatching.TSM

/-- **Equation (4)** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.3, p. 8), with the paper's `1 - e^{-Ω(n)}` made explicit. For every
`ε > 0` there are `δ > 0` and `N` such that for every instance with `e_i = 1` (finite advertisers
`A`, finite impression types `I`, edges `E ⊆ A × I`, `n = |I| ≥ N` arrivals drawn i.i.d. uniformly
from `I`), every maximum flow edge set `E_f` and every TSM colouring `(blue, red)` of it, with
probability at least `1 - e^{-δ n}`,
`OPT ≤ |A_BR| + |A_BB| + ½(|A_B| + |A_R|) + (½ - 1/e)|E_δ| + ε n`,
where `OPT` is the maximum matching of the realization graph and `E_δ` is the cut edge set of
§4.2.3. -/
theorem eq_4 :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F blue red : Finset (A × I)),
        N ≤ Fintype.card I → IsMaxFlowSet E F → IsTSMColoring F blue red →
        1 - Real.exp (-δ * Fintype.card I) ≤
          prob (Fintype.card I) (fun ω : Fin (Fintype.card I) → I =>
            (OPT E ω : ℝ) ≤
              (adsBR blue red).card + (adsBB blue red).card
                + ((adsB blue red).card + (adsR blue red).card) / 2
                + (1 / 2 - 1 / Real.exp 1) * (Edelta E F).card + ε * Fintype.card I) := by sorry

end OnlineStochMatching.TSM
