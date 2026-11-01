-- Prove2me | Theorems.Thm_MultiplayerNoCollision_no_collision_unbiased
-- name    : MultiplayerNoCollision.no_collision_unbiased
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:47.563629+00:00
-- url     : https://prove2.me/theorems/97fdaaf2-1724-45dd-8ea8-a67e363dc776
-- title:
--   §3 display — a uniform pull is collision-free with probability $(1-1/K)^{m-1}$, so $\mu_i=\mathbb E r(t)/(1-1/K)^{m-1}$
-- statement:
--   Consider the game in which all $m\ge2$ players pull a uniformly random arm in every round, with $K\ge m$ arms and rewards and seeds as in the model. Fix a round $t$, a player $j$ and an arm $i$, and let $A=A_j(t)$ and $r=r_j(t)$. Then
--   $$\mathbb E\bigl[(1-C_i(t))\,\mathbb 1\{A=i\}\bigr]=\frac{(1-1/K)^{m-1}}{K}$$
--   and
--   $$\mathbb E\bigl[r\,\mathbb 1\{A=i\}\bigr]=\mu_i\;\mathbb E\bigl[(1-C_i(t))\,\mathbb 1\{A=i\}\bigr].$$
--
--   Since $P(A=i)=1/K$, these say that, given that arm $i$ is pulled, the pull is collision-free with probability $(1-1/K)^{m-1}$ and $\mathbb E\,r=\mu_i(1-1/K)^{m-1}$. This is why the Phase-1 estimate divides by $(1-1/K)^{m-1}$.
--
--   Differences from the source:
--   - reading: for any round t that arm i is pulled: µ_i = E Y_{i,t} = E r(t)/E(1 − C_i(t)) = E r(t)/(1 − 1/K)^{m−1} → E[(1 − C_i(t)) 𝟙{A_j(t) = i}] = (1 − 1/K)^{m−1}/K and E[r_j(t) 𝟙{A_j(t) = i}] = µ_i E[(1 − C_i(t)) 𝟙{A_j(t) = i}]; reason: the expectations "given that arm i is pulled" are written against the indicator of that event; P(A_j(t) = i) = 1/K
--   - reading: provided other players are also pulling arms uniformly at random → all m players pull a uniformly random arm in every round (uniformAct); reason: this is the situation of Phase 1 in which the display is used (p.8)
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §3, Phase 1, pp.8–9 (display on p.9)

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_Policy
import Definitions.Def_MultiplayerNoCollision_profile

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **No-collision probability `(1 − 1/K)^{m−1}` and unbiasedness of the scaled reward.**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, §3, Phase 1, pp.8–9: "Note that, provided other players are also pulling arms
uniformly at random, `(1 − 1/K)^{m−1}` is precisely the probability of *not* getting a conflict for a
random pull, hence the player indeed has an unbiased estimate for `µ_i`. In other words, for any
round `t` that arm `i` is pulled and reward `r(t)` is received, since collisions and rewards are
independent, we have (recall (1))
`µ_i = E Y_{i,t} = E r(t) / E(1 − C_i(t)) = E r(t) / (1 − 1/K)^{m−1}`."

In the game where all `m` players pull a uniformly random arm in every round (`uniformAct`), for
every round `t`, player `j` and arm `i`, writing `A_j(t)` for the arm of player `j`:
1. `E[(1 − C_i(t)) 𝟙{A_j(t) = i}] = (1 − 1/K)^{m−1} / K`;
2. `E[r_j(t) 𝟙{A_j(t) = i}] = µ_i · E[(1 − C_i(t)) 𝟙{A_j(t) = i}]`.
Since `P(A_j(t) = i) = 1/K`, these are the paper's conditional expectations given that arm `i` is
pulled, multiplied by `1/K`.

**Formalization Note.** Rounds are 0-based; `µ_i = E Y_{i,0}` (`means`). The expectations
conditional on "arm `i` is pulled" are written as expectations against the indicator `𝟙{A_j(t) = i}`.
The standing assumptions `m ≥ 2` and `K ≥ m` of the paper (p.3, Assumption 1, p.4) are kept. -/
theorem no_collision_unbiased {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m K : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m ≤ K)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U)
    (t : ℕ) (j : Fin m) (i : Fin K) :
    (∫ ω, (1 - collision (profile uniformAct Y U ω t) i) *
        (if profile uniformAct Y U ω t j = i then 1 else 0) ∂P =
      (1 - 1 / (K : ℝ)) ^ (m - 1) / K) ∧
    (∫ ω, received Y (profile uniformAct Y U ω t) t ω j *
        (if profile uniformAct Y U ω t j = i then 1 else 0) ∂P =
      means P Y i * ∫ ω, (1 - collision (profile uniformAct Y U ω t) i) *
        (if profile uniformAct Y U ω t j = i then 1 else 0) ∂P) := by sorry

end MultiplayerNoCollision
