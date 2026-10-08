-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_fact_1
-- name    : OnlineStochMatching.SuggestedMatching.fact_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:47:29.715991+00:00
-- url     : https://prove2.me/theorems/df6fd54a-bec7-4070-aff2-269e9531e94a
-- title:
--   Fact 1 — occupancy of a subset of bins concentrates
-- statement:
--   Throw $n\ge1$ balls independently and uniformly into $n$ bins. For any fixed subset $B$ and any $\varepsilon>0$, let $S_B$ count its occupied bins. Then
--
--   $$\Pr\!\left[|B|(1-e^{-1})-\varepsilon n\le S_B\le |B|\left(1-e^{-1}+\frac1{en}\right)+\varepsilon n\right]\ge1-2e^{-\varepsilon^2n/2}.$$
--
--   This concentration fact controls how many advertisers of a selected matching are chosen. The printed Fact 1 has $\varepsilon n/2$ in the exponent; its Appendix A proof gives the squared exponent encoded here.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 4, Fact 1; p. 12, Appendix A, Proof of Fact 1

import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace OnlineStochMatching.SuggestedMatching

/-- Fact 1, with the squared exponent established by its Appendix A proof. -/
theorem fact_1 (n : ℕ) (hn : 0 < n) (B : Finset (Fin n))
    (ε : ℝ) (hε : 0 < ε) :
    uniformProbability (fun ω : Fin n → Fin n =>
      (B.card : ℝ) * (1 - Real.exp (-1)) - ε * (n : ℝ) ≤
        (occupiedIn n B ω : ℝ) ∧
      (occupiedIn n B ω : ℝ) ≤
        (B.card : ℝ) *
          (1 - Real.exp (-1) + 1 / (Real.exp 1 * (n : ℝ))) + ε * (n : ℝ)) ≥
      1 - 2 * Real.exp (-(ε ^ 2) * (n : ℝ) / 2) := by sorry

end OnlineStochMatching.SuggestedMatching
