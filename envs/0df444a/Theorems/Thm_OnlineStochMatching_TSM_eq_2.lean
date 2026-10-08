-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_eq_2
-- name    : OnlineStochMatching.TSM.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:35:57.012158+00:00
-- url     : https://prove2.me/theorems/cc2f2457-2609-449a-8348-e3cfe004ae8d
-- title:
--   Equation (2) — w.h.p. ALG $\ge (1-1/e^2)|A_{BB}| + (1-2/e^2)|A_{BR}| + (1-3/(2e))(|A_B|+|A_R|) - 4\varepsilon n$
-- statement:
--   Consider the online stochastic matching problem with $e_i = 1$: a finite bipartite graph $G = (A, I, E)$, and $n = |I|$ arrivals whose types are drawn independently and uniformly from $I$. Let $E_f$ be the edge set of an integral maximum flow of the boosted flow graph, blue/red a TSM colouring of it, and $\mathrm{ALG}$ the number of arrivals assigned by the two suggested matchings algorithm.
--
--   For every $\varepsilon > 0$ there are $\delta > 0$ and $N$ such that, whenever $n \ge N$, for every such instance, $E_f$ and colouring, with probability at least $1 - e^{-\delta n}$,
--   $$\mathrm{ALG} \;\ge\; \Big(1 - \frac1{e^2}\Big)|A_{BB}| + \Big(1 - \frac2{e^2}\Big)|A_{BR}| + \Big(1 - \frac3{2e}\Big)\big(|A_B| + |A_R|\big) - 4\varepsilon n.$$
--
--   This is the lower bound on the algorithm's value that is compared with the upper bound (4) on OPT in the proof of Theorem 5.
--
--   **Formalization Note** The paper writes "with high probability"; in the proof of Theorem 5 (p. 9) this is $1 - e^{-\Omega(n)}$. The statement makes it explicit: $\delta$ and $N$ depend on $\varepsilon$ only, and are chosen before the instance, so they are uniform over all graphs and all sizes of $A$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 7, Section 4.2.2, equation (2); probability 1 − e^{−Ω(n)} from p. 9, Section 4.2.4

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Algorithm

namespace OnlineStochMatching.TSM

/-- **Equation (2)** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §4.2.2, p. 7), with the paper's "with high probability" made explicit.
For every `ε > 0` there are `δ > 0` and `N` such that for every instance with `e_i = 1` (finite
advertisers `A`, finite impression types `I`, edges `E ⊆ A × I`, `n = |I| ≥ N` arrivals drawn i.i.d.
uniformly from `I`), every maximum flow edge set `E_f` and every TSM colouring `(blue, red)` of it,
with probability at least `1 - e^{-δ n}`,
`ALG ≥ (1 - 1/e²)|A_BB| + (1 - 2/e²)|A_BR| + (1 - 3/(2e))(|A_B| + |A_R|) - 4 ε n`. -/
theorem eq_2 :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F blue red : Finset (A × I)),
        N ≤ Fintype.card I → IsMaxFlowSet E F → IsTSMColoring F blue red →
        1 - Real.exp (-δ * Fintype.card I) ≤
          prob (Fintype.card I) (fun ω : Fin (Fintype.card I) → I =>
            (1 - 1 / Real.exp 1 ^ 2) * (adsBB blue red).card
                + (1 - 2 / Real.exp 1 ^ 2) * (adsBR blue red).card
                + (1 - 3 / (2 * Real.exp 1)) * ((adsB blue red).card + (adsR blue red).card)
                - 4 * ε * Fintype.card I ≤
              (ALG blue red ω : ℝ)) := by sorry

end OnlineStochMatching.TSM
