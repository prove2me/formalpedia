-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_theorem_3
-- name    : HordijkKallenbergLP.SingleLP.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:53:11.1207+00:00
-- url     : https://prove2.me/theorems/b4d26115-f5e7-4dca-b09f-6ac8c661ba0d
-- title:
--   Theorem 3 (Blackwell) — v^α(f^∞) − φ(f^∞)/(1−α) → D(f)r(f) as α ↑ 1
-- statement:
--   For every pure and stationary policy $f^\infty$ and every state $i\in E$,
--   $$\lim_{\alpha\uparrow1}\Big[v_i^\alpha(f^\infty)-\frac{\varphi_i(f^\infty)}{1-\alpha}\Big]=\big(D(f)r(f)\big)_i ,$$
--   where $D(f)=(I-P(f)+P^*(f))^{-1}-P^*(f)$ is the deviation matrix of $P(f)$.
--
--   This is the first two terms of Blackwell's expansion of the discounted value near $\alpha=1$; Theorem 5 is derived from it.
--
--   **Formalization Note** The limit is one-sided, $\alpha\to1$ from below.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 3

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 3 (Blackwell).** For all `i ∈ E` and any pure and stationary policy `f^∞`,
`lim_{α↑1} [v_i^α(f^∞) − φ_i(f^∞)/(1 − α)] = (D(f) r(f))_i`, where
`D(f) = (I − P(f) + P*(f))⁻¹ − P*(f)`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 355, Theorem 3.

**Formalization Note.** `α ↑ 1` is the left neighbourhood filter `𝓝[<] 1`. -/
theorem theorem_3 (M : StationaryMDP S A) [Nonempty S] (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (i : S) :
    Tendsto (fun α : ℝ => discValue (stationaryPolicy M f hf) α i
        - gainInf (stationaryPolicy M f hf) i / (1 - α))
      (𝓝[<] 1) (𝓝 ((deviationMatrix (transMatrix M f) *ᵥ rewardVec M f) i)) := by sorry

end HordijkKallenbergLP.SingleLP
