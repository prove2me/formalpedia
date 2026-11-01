-- Prove2me | Theorems.Thm_MultiplayerNoCollision_lemma_7
-- name    : MultiplayerNoCollision.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:40.724407+00:00
-- url     : https://prove2.me/theorems/ad297580-d6c4-42ed-b258-e4adb24392ea
-- title:
--   Lemma 7 — w.p. $\ge1-1/mT$, Phase 3 takes at most $4m\log(m^2T)/\Delta$ rounds for all players
-- statement:
--   All $m\ge2$ players run Algorithm 1 for $T\ge1$ rounds, with $K\ge m+1$ arms and rewards and seeds as in the model, and $\Delta=\mu_{(m)}-\mu_{(m+1)}>0$. Let $E$ be the event of Lemma 6(i): every player whose Phase 1 ends by round $T$ has the $m$ best arms as her list $G$. Then
--   $$P\Bigl(E\cap\Bigl\{\exists j:\ \#\{t<T:\ \text{player } j \text{ is in Phase 3 in round } t\}>\frac{4m\log(m^2T)}{\Delta}\Bigr\}\Bigr)\le\frac{1}{mT}.$$
--
--   So on the good event of Lemma 6, with probability at least $1-1/(mT)$ the musical-chairs phase of every player is short.
--
--   Differences from the source:
--   - reading: with probability at least 1 − 1/mT, Phase 3 takes at most 4m log(m²T)/∆ rounds for all players → P(E ∩ {some player spends more than 4m log(m²T)/∆ of the rounds t < T in Phase 3}) ≤ 1/(mT), with E the event of Lemma 6(i); reason: the proof (pp.12–13) needs every G to be the best-m set ("hence a ≥ 1", "∆ ≤ µ_m is a lower bound on the probability that that arm produces a positive reward"); a G containing an arm of mean 0 can block a player forever; the T-round game counts only rounds t < T
--   - reading: 1/mT → 1/(mT); reason: the proof (p.11) takes a union bound over m players of failure probability 1/(m²T); the other parse (1/m)·T exceeds 1
--   - encoding: K ≥ m (Assumption 1) → K ≥ m + 1; reason: ∆ = µ_m − µ_{m+1} and the stopping rule of Algorithm 1 need an (m+1)-th arm; only the undefined case K = m is excluded
--   - encoding: bounds with ∆ in a denominator → hypothesis ∆ > 0; reason: the bounds divide by ∆; only the undefined case ∆ = 0 is excluded
--   - encoding: Algorithm 1 with MusicalChairs1 (p.10), state µ̂, τ, Best-m-arms, occupied arm → algorithm1: a rule of (round, own history, own seed); uniform arm = ⌊K u⌋ clamped, uniform arm of G = the ⌊|G| u⌋-th element of G in increasing order (clamped); reason: every state variable of Algorithm 1 is a deterministic function of the own history; the seed maps push the uniform law to the uniform law on [K] and on G
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Lemma 7, p.12

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_kthLargest
import Definitions.Def_MultiplayerNoCollision_algorithm1

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Lemma 7 (MusicalChairs1 is fast).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Lemma 7, p.12: "With probability at least `1 − 1/mT`, Phase 3 takes at most
`4m log(m²T)/∆` many rounds for all players."

All `m` players run Algorithm 1 for `T` rounds and `∆ = µ_m − µ_{m+1} > 0`. Let `E` be the event of
Lemma 6(i): every player whose Phase 1 ends by round `T` has the set of the `m` best arms as her
list `G`. Then the probability that `E` holds and some player spends more than `4m log(m²T)/∆` of
the rounds `0, …, T − 1` in Phase 3 is at most `1/(mT)`.

**Formalization Note.** The proof (pp.12–13) uses that every `G` is the set of the best `m` arms
("there are still `a` unoccupied arms available for her … hence `a ≥ 1`", and "`∆ ≤ µ_m` is a lower
bound on the probability that that arm produces a positive reward"), which is Lemma 6(i); the
statement is read on that event. Phase-3 rounds are counted among the `T` rounds of the game.
`1/mT` is `1/(mT)`; `log` is the natural logarithm; `∆ > 0` because the bound divides by `∆`. -/
theorem lemma_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m K T : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m + 1 ≤ K) (hT : 1 ≤ T)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U)
    (hΔ : 0 < gap (means P Y) m) :
    P.real {ω | (∀ (j : Fin m) (τ : ℕ), stopRound m K T Y U ω j = some τ →
          bestArmsOf m K T Y U ω j τ = topSet (means P Y) m) ∧
        ∃ j : Fin m, 4 * m * Real.log ((m : ℝ) ^ 2 * T) / gap (means P Y) m <
          (phase3Rounds m K T Y U ω j : ℝ)} ≤
      1 / ((m : ℝ) * T) := by sorry

end MultiplayerNoCollision
