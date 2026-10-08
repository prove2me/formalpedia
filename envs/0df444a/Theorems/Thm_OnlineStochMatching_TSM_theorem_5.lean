-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_theorem_5
-- name    : OnlineStochMatching.TSM.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:36:09.208983+00:00
-- url     : https://prove2.me/theorems/7ec94e69-a198-4d8f-9c42-cc1b648b87e7
-- title:
--   Theorem 5 — when OPT $\ge cn$, the TSM algorithm achieves ALG $\ge (\alpha - \varepsilon)$OPT w.p. $1 - e^{-\delta n}$, $\alpha = \frac{1 - 2/e^2}{4/3 - 2/(3e)} > 1 - 1/e$
-- statement:
--   Consider the online stochastic matching problem with $e_i = 1$: a finite bipartite graph $G = (A, I, E)$ of advertisers and impression types, and $n = |I|$ arrivals whose types are drawn independently and uniformly from $I$. The **two suggested matchings (TSM) algorithm** computes the edge set $E_f$ of an integral maximum flow of the boosted flow graph (source and sink capacities 2, edge capacities 1), colours $E_f$ blue and red by the rules of Section 4.2.1, and then assigns the first arrival of each type along its blue edge and the second along its red edge, whenever the advertiser is still free. Let $\mathrm{ALG}$ be the number of arrivals it assigns and $\mathrm{OPT}$ the size of a maximum matching of the realization graph. Set
--   $$\alpha = \frac{1 - 2/e^2}{4/3 - 2/(3e)} \approx 0.67029.$$
--   Then:
--   1. every maximum flow edge set $E_f$ admits a colouring that follows the rules, so the algorithm is well defined;
--   2. for every $\varepsilon > 0$ and $c > 0$ there are $\delta > 0$ and $N$ such that, whenever $n \ge N$, for every instance, every maximum flow edge set $E_f$ and every colouring that follows the rules, with probability at least $1 - e^{-\delta n}$,
--   $$\mathrm{OPT} \ge c\,n \;\Longrightarrow\; \mathrm{ALG} \ge (\alpha - \varepsilon)\,\mathrm{OPT};$$
--   3. $\alpha > 1 - 1/e$.
--
--   This is the paper's main algorithmic result: with a known i.i.d. arrival distribution, an online algorithm beats the ratio $1 - 1/e$, which is optimal for adversarial arrivals and is all that the single suggested matching algorithm achieves.
--
--   **Formalization Note** The paper writes "$\mathrm{ALG}/\mathrm{OPT} - \epsilon \ge \alpha$"; its proof ends with $\mathrm{ALG}/\mathrm{OPT} + \epsilon \ge \alpha$ (p. 9), and the tightness family of Section 4.2.5 has ratio close to $\alpha$, so the printed form is a slip and the statement uses $\alpha - \varepsilon$. "With probability at least $1 - e^{-\Omega(n)}$, as long as $\mathrm{OPT} = \Omega(n)$" is read as: for every $c > 0$, the event "$\mathrm{OPT} \ge cn$ implies the ratio bound" has probability at least $1 - e^{-\delta n}$, with $\delta$ and $N$ depending on $\varepsilon$ and $c$ only. The ratio is multiplied out, so no division by $\mathrm{OPT}$ occurs. The statement covers the case $e_i = 1$, which the paper analyses throughout Section 4.2; the reduction for general integer $e_i$ and the tightness sentence of Theorem 5 are not part of it.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 6, Theorem 5 (first sentence, case e_i = 1); proof p. 9, Section 4.2.4

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Algorithm

namespace OnlineStochMatching.TSM

/-- **Theorem 5**, first sentence, for `e_i = 1` (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online
Stochastic Matching: Beating 1-1/e*, arXiv:0905.4100v1, §4.2, p. 6; proof §4.2.4, p. 9). Let
`α = (1 - 2/e²)/(4/3 - 2/(3e))`. The statement is the conjunction of
* (a) the two suggested matchings algorithm is well defined: every maximum flow edge set `E_f` of
  the boosted flow graph admits a TSM colouring;
* (b) for every `ε > 0` and `c > 0` there are `δ > 0` and `N` such that for every instance with
  `e_i = 1` and `n = |I| ≥ N`, every maximum flow edge set `E_f` and every TSM colouring of it, with
  probability at least `1 - e^{-δ n}` over the `n` i.i.d. uniform arrivals: if `OPT ≥ c n` then
  `ALG ≥ (α - ε) OPT`;
* (c) `α > 1 - 1/e`.

Correction to the page: the theorem prints `ALG/OPT - ε ≥ α`; its proof ends with
`ALG/OPT + ε ≥ α` (p. 9), and the tightness family of §4.2.5 has ratio close to `α`, so the
printed form is false. "As long as OPT = Ω(n)" is the event `OPT ≥ c n` with `c > 0` arbitrary;
`δ` and `N` depend on `ε` and `c` only. -/
theorem theorem_5 :
    (∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F : Finset (A × I)),
        IsMaxFlowSet E F → ∃ blue red : Finset (A × I), IsTSMColoring F blue red) ∧
    (∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F blue red : Finset (A × I)),
        N ≤ Fintype.card I → IsMaxFlowSet E F → IsTSMColoring F blue red →
        1 - Real.exp (-δ * Fintype.card I) ≤
          prob (Fintype.card I) (fun ω : Fin (Fintype.card I) → I =>
            c * Fintype.card I ≤ (OPT E ω : ℝ) →
              (alpha - ε) * (OPT E ω : ℝ) ≤ (ALG blue red ω : ℝ))) ∧
    1 - Real.exp (-1) < alpha := by sorry

end OnlineStochMatching.TSM
