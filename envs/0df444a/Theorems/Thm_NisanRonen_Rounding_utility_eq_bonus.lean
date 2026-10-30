-- Prove2me | Theorems.Thm_NisanRonen_Rounding_utility_eq_bonus
-- name    : NisanRonen.Rounding.utility_eq_bonus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:26:33.216519+00:00
-- url     : https://prove2.me/theorems/310b1c86-abf0-44f8-ba8d-e755ca3dd979
-- title:
--   Under the rounding mechanism, an agent's utility equals its bonus
-- statement:
--   Fix an allocation algorithm $f$ on rounded instances and a grid step $\delta$. For every strategy profile, with declarations $d$, allocation $x = x_f(d)$ and actual times $\tilde t$, and every agent $i$, the utility of agent $i$ under the rounding mechanism equals its bonus:
--
--   $$
--   u^i = -\hat g\big(x, \mathrm{corr}^i(x, d, \tilde t)\big).
--   $$
--
--   The compensation $\sum_{j \in x^i} \tilde t_j$ exactly cancels the agent's cost $v^i = -\sum_{j \in x^i} \tilde t_j$, so the agent's incentives are those of the bonus alone.
--
--   Differences from the source:
--   - encoding: agents 1, …, n and tasks 1, …, k → `Fin n` and `Fin k`, i.e. 0, …, n − 1 and 0, …, k − 1; reason: Lean indexing convention; the same instances
--   - encoding: n agents → `[NeZero n]`, i.e. n ≥ 1; reason: with no agents and at least one task there is no allocation and no make-span; the paper's n agents are at least one
--   - reading: the argument of Claim 5.2 for the exact bonus −g(x(t), corr^i(x(t), t, t̃)) of Definition 23 → the same step for the rounded bonus −ĝ(x(t̂), corr^i(x(t), t, t̃)) of Definition 34; reason: the proof sketch of Theorem 5.9 (p. 193) applies "Arguments similar to those in 5.1" to the rounding mechanism; this is that argument's step for ĝ
--   - encoding: the bonus uses the allocation x(t̂) and the compensation x(t) (Def. 34) → one allocation `allocOf f δ d`, computed from the δ-unit instance `units δ d`; reason: the algorithm reads only the rounded instance, and ⌈roundUp δ v / δ⌉ = ⌈v / δ⌉, so x(t̂) = x(t)
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, proof of Claim 5.2, p. 188 (PDF p. 23): "Observing that the utility of an agent equals its bonus", applied to the payment of Definition 34, p. 193 (PDF p. 28)

import Mathlib
import Definitions.Def_NisanRonen_Rounding_utility

namespace NisanRonen.Rounding

/-- **The utility of an agent equals its bonus** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), proof of Claim 5.2, p. 188:
"Observing that the utility of an agent equals its bonus"), for the payment of Definition 34
(p. 193). For every allocation algorithm `f`, grid `δ`, strategy profile `s` and agent `i`, with
declarations `d`, allocation `x = x(d)` and actual times `t̃`, agent `i`'s utility is
`−ĝ(x, corr^i(x, d, t̃))`: the compensation cancels the valuation. -/
theorem utility_eq_bonus {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) :
    utility f δ s i =
      - roundedMakespan δ (allocOf f δ (fun l => (s l).decl))
          (corr i (allocOf f δ (fun l => (s l).decl)) (fun l => (s l).decl)
            (actualTimes f δ s)) := by sorry

end NisanRonen.Rounding
