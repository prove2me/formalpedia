-- Prove2me | Theorems.Thm_MultiplayerNoCollision_lemma_5
-- name    : MultiplayerNoCollision.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:49.930546+00:00
-- url     : https://prove2.me/theorems/24afc09a-6a10-4b38-93ec-240166cd9fd5
-- title:
--   Lemma 5 — $P\{\exists i,t\le T:|\hat\mu_{i,t}-\mu_i|>\sqrt{g/t}\}<3KT e^{-g/128K}$
-- statement:
--   Consider the game in which all $m\ge2$ players pull a uniformly random arm in every round, with $K\ge m$ arms, $T\ge1$ rounds, and rewards and seeds as in the model. Fix a player and let $\hat\mu_{i,t}$ be her scaled estimate of $\mu_i$ after $t$ rounds. With $g=128K\log(3Km^2T^2)$,
--   $$P\Bigl\{\exists i\in[K],\ t\in[T]:\ |\hat\mu_{i,t}-\mu_i|>\sqrt{g/t}\Bigr\}<3KT\exp\!\left(-\frac{g}{128K}\right).$$
--
--   With this choice of $g$ the right side equals $1/(m^2T)$, so after a union bound over the $m$ players all estimates are uniformly accurate with probability at least $1-1/(mT)$. This is the input of Lemma 6.
--
--   Differences from the source:
--   - reading: "after t rounds of Phase 1", for t ∈ [T] → the game in which all m players pull uniformly random arms for all rounds; the estimate from the player's history of the first t rounds, t ∈ {1, …, T}; reason: Phase 1 is analysed "provided other players are also pulling arms uniformly at random" (p.8), and the lemma ranges over all t ∈ [T]; this is the process the proof treats
--   - reading: exp(−g/128K) → exp(−g/(128K)); reason: the proof derives it from exp(−t/8K) with t > g/16 (p.11)
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Lemma 5, p.11

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_Policy
import Definitions.Def_MultiplayerNoCollision_profile
import Definitions.Def_MultiplayerNoCollision_phase1Estimate
import Definitions.Def_MultiplayerNoCollision_algorithm1

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Lemma 5 (the scaled estimates are uniformly accurate).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Lemma 5, p.11: "Consider any fixed player and let `µ̂_{i,t}` denote her
estimated mean for arm `i` after `t` rounds of Phase 1. Then we have
`P{∃ i ∈ [K], t ∈ [T] : |µ̂_{i,t} − µ_i| > √(g/t)} < 3KT exp(−g/128K)`."

In the game where all `m` players pull a uniformly random arm in every round (`uniformAct`, the
situation of Phase 1, p.8: "provided other players are also pulling arms uniformly at random"), for
every player `j`, with `g = 128 K log(3 K m² T²)` and `µ̂_{i,t}` the scaled estimate
`phase1Estimate` computed from player `j`'s history of the first `t` rounds,
`P{∃ i, ∃ t ∈ {1, …, T} : |µ̂_{i,t} − µ_i| > √(g/t)} < 3 K T exp(−g/(128K))`.

**Formalization Note.** Rounds are 0-based, so "after `t` rounds" is the history of rounds
`0, …, t − 1`; `t` ranges over `{1, …, T}`. An arm never pulled has estimate `0` (Algorithm 1,
line 2). `exp(−g/128K)` is `exp(−g/(128K))`. The standing assumptions `m ≥ 2`, `K ≥ m`, `T ≥ 1`
(pp.3–4) are kept. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m K T : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m ≤ K) (hT : 1 ≤ T)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U) (j : Fin m) :
    P.real {ω | ∃ i : Fin K, ∃ t ∈ Finset.Icc 1 T,
        Real.sqrt (gParam m K T / t) <
          |phase1Estimate m K (history uniformAct Y U ω j t) i - means P Y i|} <
      3 * K * T * Real.exp (-gParam m K T / (128 * K)) := by sorry

end MultiplayerNoCollision
