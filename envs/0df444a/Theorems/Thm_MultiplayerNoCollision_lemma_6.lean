-- Prove2me | Theorems.Thm_MultiplayerNoCollision_lemma_6
-- name    : MultiplayerNoCollision.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:39.516071+00:00
-- url     : https://prove2.me/theorems/2fac3bea-00ca-41c3-8a42-a5a9db1137a2
-- title:
--   Lemma 6 — w.p. $\ge1-1/mT$ all players learn the best $m$ arms, $g/\Delta^2\le\tau\le25g/\Delta^2$, Phases 1–2 end by $625g/\Delta^2$
-- statement:
--   All $m\ge2$ players run Algorithm 1 for $T\ge1$ rounds, with $K\ge m+1$ arms and rewards and seeds as in the model. Let $\Delta=\mu_{(m)}-\mu_{(m+1)}>0$ and $g=128K\log(3Km^2T^2)$. For player $j$ let $\tau_j\in\{1,\dots,T\}\cup\{\infty\}$ be the length of her Phase 1 ($\infty$ if it is not over by round $T$) and $G_j$ her list of best arms. With probability at least $1-1/(mT)$, for every player $j$:
--
--   1. if $\tau_j<\infty$, then $G_j$ is the set of the $m$ arms with the largest means;
--   2. $g/\Delta^2\le\tau_j$ and $\min(\tau_j,T)\le 25g/\Delta^2$;
--   3. $\min(25\tau_j,T)\le 625g/\Delta^2$, i.e. Phases 1 and 2 of every player are over after at most $625g/\Delta^2$ rounds.
--
--   Phase 2 lasts long enough that every other player finishes Phase 1 while still facing uniformly random collisions, which is what keeps the estimates unbiased.
--
--   Differences from the source:
--   - reading: τ (the round at which Phase 1 finishes), "after at most … many rounds" → τ_j ∈ {1, …, T} ∪ {∞} in the T-round game; the upper bounds read as min(τ_j, T) ≤ 25g/∆² and min(25τ_j, T) ≤ 625g/∆²; reason: the game has T rounds and Lemma 5 covers t ∈ [T] only; at m = 2, K = 3, T = 2 the stopping threshold 3√(g/τ) ≥ 92 exceeds every estimated gap, so τ = ∞ surely and "τ ≤ 25g/∆²" read with τ = ∞ would be false; when the bounds are below T this is the printed claim
--   - reading: 1/mT → 1/(mT); reason: the proof (p.11) takes a union bound over m players of failure probability 1/(m²T); the other parse (1/m)·T exceeds 1
--   - encoding: K ≥ m (Assumption 1) → K ≥ m + 1; reason: ∆ = µ_m − µ_{m+1} and the stopping rule of Algorithm 1 need an (m+1)-th arm; only the undefined case K = m is excluded
--   - encoding: bounds with ∆ in a denominator → hypothesis ∆ > 0; reason: the bounds divide by ∆; only the undefined case ∆ = 0 is excluded
--   - encoding: Algorithm 1 with MusicalChairs1 (p.10), state µ̂, τ, Best-m-arms, occupied arm → algorithm1: a rule of (round, own history, own seed); uniform arm = ⌊K u⌋ clamped, uniform arm of G = the ⌊|G| u⌋-th element of G in increasing order (clamped); reason: every state variable of Algorithm 1 is a deterministic function of the own history; the seed maps push the uniform law to the uniform law on [K] and on G
--   - encoding: rounds t = 1, …, T, arms i ∈ [K], players j ∈ [m] → 0-based rounds t = 0, …, T − 1, arms Fin K, players Fin m; reason: indexing only; paper round t is Lean round t − 1
--   - encoding: "the strategy can randomize" (p.4) → player j uses in round t a private seed U_{j,t} uniform on [0,1]; all seeds are independent and independent of the rewards; reason: every randomized choice of the paper (a uniform arm, a uniform arm of G) is a measurable function of one uniform seed; the players do not communicate
--   - generalization: the sequences {Y_{i,t}}_{t≥1} are i.i.d. (dependence between arms not stated) → the reward vectors (Y_{1,t}, …, Y_{K,t}) are i.i.d. over t; arbitrary dependence across arms within a round; reason: contains the model with all Y_{i,t} independent; the per-arm-only reading (e.g. Y_{2,t+1} = Y_{1,t}) breaks the independence of the current reward from the history that the proof uses on pp.9 and 12
--   - encoding: Y_{A_j(t),t} supported on [0,1]; random variables → Y_{i,t} measurable with 0 ≤ Y_{i,t} ≤ 1 at every outcome; reason: modification on a null set changes neither the law nor the play up to a null set
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Lemma 6, p.11

import Mathlib
import Definitions.Def_MultiplayerNoCollision_GameModel
import Definitions.Def_MultiplayerNoCollision_kthLargest
import Definitions.Def_MultiplayerNoCollision_algorithm1

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Lemma 6 (Phases 1–2 identify the best `m` arms and do not last long).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Lemma 6, p.11: "With probability at least `1 − 1/mT`, the following are true.
(i) All players have learned the best `m` arms by end of their Phase 1. (ii) We have
`g/∆² ≤ τ ≤ 25g/∆²` for all players (where we recall that `τ` is the round at which phase 1
finishes). (iii) The first two phases are finished for all players after at most `625g/∆²` many
rounds."

All `m` players run Algorithm 1 for `T` rounds, `∆ = µ_m − µ_{m+1} > 0` is the gap of the sorted
means and `g = 128 K log(3 K m² T²)`. Let `τ_j ∈ {1, …, T} ∪ {∞}` be player `j`'s Phase-1 length
(`stopRound`; `∞` if Phase 1 is not over by round `T`) and `G_j` her best-`m`-arms list. Then with
probability at least `1 − 1/(mT)`, for every player `j`:
1. if `τ_j < ∞` then `G_j` is the set of the `m` arms with the largest means;
2. `g/∆² ≤ τ_j` and `min(τ_j, T) ≤ 25g/∆²`;
3. `min(25τ_j, T) ≤ 625g/∆²` (Phases 1–2 of player `j` occupy rounds `< 25τ_j`).

**Formalization Note.** The game has `T` rounds, so `τ_j` is read in `{1, …, T} ∪ {∞}` and the upper
bounds of (ii)–(iii) are read for the rounds of the game: "no round `≤ T` after `25g/∆²` (resp.
`625g/∆²`) is in Phase 1 (resp. Phases 1–2)". When `25g/∆² < T` (resp. `625g/∆² < T`) this is the
printed bound. `τ_j = ∞` is `none`, and `min(τ_j, T)` is `getD T`. `1/mT` is `1/(mT)`. `∆ > 0` is
assumed because the bounds divide by `∆`. -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m K T : ℕ) [NeZero K] (hm : 2 ≤ m) (hK : m + 1 ≤ K) (hT : 1 ≤ T)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (hmodel : GameModel P Y U)
    (hΔ : 0 < gap (means P Y) m) :
    1 - 1 / ((m : ℝ) * T) ≤ P.real {ω | ∀ j : Fin m,
      (∀ τ : ℕ, stopRound m K T Y U ω j = some τ →
        bestArmsOf m K T Y U ω j τ = topSet (means P Y) m) ∧
      (∀ τ : ℕ, stopRound m K T Y U ω j = some τ →
        gParam m K T / gap (means P Y) m ^ 2 ≤ τ) ∧
      (((stopRound m K T Y U ω j).getD T : ℕ) : ℝ) ≤
        25 * gParam m K T / gap (means P Y) m ^ 2 ∧
      ((min (25 * (stopRound m K T Y U ω j).getD T) T : ℕ) : ℝ) ≤
        625 * gParam m K T / gap (means P Y) m ^ 2} := by sorry

end MultiplayerNoCollision
