-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_4_40
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_4_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:02:04.702655+00:00
-- url     : https://prove2.me/theorems/b4f373f0-a808-4988-a636-0a871525f9e3
-- title:
--   Theorem 4.40 — for p < 1/3, P(K) → 1: red edges can be fractionally rerouted over two-white-edge paths
-- statement:
--   Colour each edge of the complete graph on $K$ nodes independently red with probability $p\in(0,1)$ and white otherwise. Each red pair uses its red edge and must divide one further unit of traffic among the two-edge paths through tandem nodes joined to both of its ends by white edges; every white edge has unit capacity. Let $P(K)$ be the probability that this can be done simultaneously for every red edge without exceeding the capacity of any white edge. If $p<1/3$, then
--   $$P(K)\to1\qquad(K\to\infty).$$
--
--   The result, due to Hajek, shows that in a large fully connected network a random set of communicating pairs whose density is below one third can almost surely be served using only idle edges.
--
--   **Formalization Note** $P(K)$ is `whiteRoutingProb p K`, the finite sum of the product Bernoulli weights over the white-routable colourings.
--
--   Differences from the source:
--   - encoding: probability under independent red/white colouring → finite sum over colourings Edge K → Bool of ∏_e (p if red else 1 − p); reason: the product Bernoulli measure on a finite set; same value
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 357, Theorem 4.40; model and P(K) on pp. 356–357, §4.6

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_RedWhite

open Filter Topology

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 4.40** (due to Hajek). For `p < 1/3`, `P(K) → 1` as `K → ∞`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 357, Theorem 4.40; the model and `P(K)` on pp. 356–357, §4.6.

**Formalization Note.** `whiteRoutingProb p K` is `P(K)`: the probability, when each edge of
the complete graph on `K` nodes is independently red with probability `p`, that every red pair
can split its unit of excess traffic over two-white-edge paths with no white edge carrying
more than one unit (`WhiteRoutable`). The parameter range is the paper's `p ∈ (0, 1)` (p. 356)
intersected with `p < 1/3`. -/
theorem theorem_4_40 (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 3) :
    Tendsto (fun K : ℕ => whiteRoutingProb p K) atTop (𝓝 1) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
