-- Prove2me | Theorems.Thm_OnlineStochMatching_TSM_fact_1
-- name    : OnlineStochMatching.TSM.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:35:20.424595+00:00
-- url     : https://prove2.me/theorems/485abf0f-9f7b-4c4b-b754-113594f54e3c
-- title:
--   Fact 1 — occupancy of a subset of bins concentrates around $|B|(1 - 1/e)$
-- statement:
--   Throw $n$ balls independently and uniformly into $n$ bins. Let $B$ be a fixed set of bins and let $S$ be the number of bins of $B$ that receive at least one ball. Then for every $\varepsilon > 0$, with probability at least $1 - 2e^{-\varepsilon^2 n/2}$,
--   $$|B|\Big(1 - \frac1e\Big) - \varepsilon n \;\le\; S \;\le\; |B|\Big(1 - \frac1e + \frac1{en}\Big) + \varepsilon n.$$
--
--   This concentration bound is used twice in the analysis of the two suggested matchings algorithm: to lower-bound the number of advertisers in $A_B$ that are assigned, and to upper-bound the number of crossing edges of $E_\delta$ whose impression type arrives.
--
--   **Formalization Note** The paper prints the failure probability as $2e^{-\varepsilon n/2}$. Its own proof (Appendix A, p. 12) gives $2e^{-\varepsilon^2 n/2}$, and the printed form is false for small $\varepsilon$ and large $n$, since $S$ has standard deviation of order $\sqrt n$. The statement uses the exponent of the proof. The bins are `Fin n` and a ball placement is a function `Fin n → Fin n`.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Fact 1 (Section 2.1); restated with proof p. 12, Appendix A

import Mathlib
import Definitions.Def_OnlineStochMatching_TSM_Model

namespace OnlineStochMatching.TSM

open Finset

/-- **Fact 1** (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating
1-1/e*, arXiv:0905.4100v1, §2.1, p. 4; proof App. A, p. 12). Throw `n` balls i.i.d. uniformly into
`n` bins (`balls t` is the bin of ball `t`), fix a set `B` of bins, and let `S` be the number of
bins of `B` that receive at least one ball. For every `ε > 0`, with probability at least
`1 - 2 exp(-ε² n / 2)`,
`|B| (1 - 1/e) - ε n ≤ S ≤ |B| (1 - 1/e + 1/(e n)) + ε n`.

Correction to the page: the statement prints the failure probability as `2 e^{-ε n / 2}`; its own
proof (App. A, p. 12) gives `2 e^{-ε² n / 2}`, and the printed form is false for small `ε` and
large `n`. -/
theorem fact_1 (n : ℕ) (B : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-(ε ^ 2 * n / 2)) ≤
      prob n (fun balls : Fin n → Fin n =>
        (B.card : ℝ) * (1 - 1 / Real.exp 1) - ε * n ≤
            ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ∧
          ((B.filter fun b => ∃ t, balls t = b).card : ℝ) ≤
            (B.card : ℝ) * (1 - 1 / Real.exp 1 + 1 / (Real.exp 1 * n)) + ε * n) := by sorry

end OnlineStochMatching.TSM
