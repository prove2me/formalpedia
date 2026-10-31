-- Prove2me | Theorems.Thm_FoundationsRL_LSVI_proposition_46
-- name    : FoundationsRL.LSVI.proposition_46
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:09.560689+00:00
-- url     : https://prove2.me/theorems/af004f13-0ff4-4cad-a2b6-57275d2ee4c1
-- title:
--   Proposition 46, p. 134 — LSVI-UCB has regret $\lesssim H\sqrt{d^3T\log(HT/\delta)\log(1+T/d)}$ in low-rank MDPs (corrected: $HT\ge2$, factor $\log(1+T/d)$)
-- statement:
--   There is a numerical constant $c_0>0$ such that for every $c\ge c_0$ there is a constant $C$ with the following property. Let $M$ be a low-rank MDP with known features $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ and horizon $H$, let $T$ be the number of episodes with $HT\ge2$, and let $\delta>0$. Run LSVI-UCB with
--   $$
--   R=c\cdot d^2\log(HT/\delta),\qquad \rho=2\sqrt d.
--   $$
--   Then, with probability at least $1-\delta$,
--   $$
--   \mathrm{Reg}=\sum_{t=1}^T f^M(\pi_M)-f^M(\hat\pi^t)\le C\,H\sqrt{d^3\,T\log(HT/\delta)\log(1+T/d)}.\tag{7.8}
--   $$
--
--   The bound does not depend on the number of states or actions, which may be infinite: the low-rank structure (7.3) replaces the size of the state space by the feature dimension $d$. It extends optimism from tabular reinforcement learning (UCB-VI) and from linear bandits (LinUCB) to reinforcement learning with linear function approximation.
--
--   Differences from the source:
--   - encoding: state space S, transitions summed as Σ_{s'} (p. 132), A large or infinite → S a countable type with P^M_h(· | s, a) a probability mass function; A an arbitrary type; reason: the book's Σ_{s'} presupposes a countable S; no finiteness is assumed
--   - correction: "If any δ > 0", no condition on H and T → HT ≥ 2; reason: the printed proposition is false at H = T = 1: H = T = 1, d = 2, one state s₀, actions a₁, a₂ with ϕ(a₁) = e₁, ϕ(a₂) = e₂, μ_1(s₀) = (1, 1), w_1 = (0, 1/2), deterministic rewards; θ̂^1_1 = (1, 0) minimizes the empty objective over B(2√2), so Q̄^1_1(a₁) = 1 > Q̄^1_1(a₂) = √R and the greedy action a₁ has regret 1/2, while log(HT/δ) = log(1/δ) → 0 as δ ↑ 1; so Reg = 1/2 with probability 1 while C·H√(d³T log(HT/δ)) → 0, and the event fails with probability 1 > δ for δ close to 1
--   - correction: (7.8), Reg ≲ H√(d³T log(HT/δ)), with one logarithm → Reg ≲ H√(d³T log(HT/δ) log(1 + T/d)); reason: the printed rate is false for every c and C, with probability 1: H = 1, d = 3, δ = 1/2, one state s₀, deterministic rewards, arms 0, 1, …, T with ϕ(0) = (1/√2, 0, 0), ϕ(n) = (1/√2, −Δ, ε_n), w_1 = (√2, 1, 0), μ_1(s₀) = (√2, 0, 0), so P = 1, arm 0 has reward 1 and arm n ≥ 1 has reward 1 − Δ, where R = 9c log(2T), σ² = log T/(2T), Δ = σ√R, ε_n² = σ²(1 + σ²)^(n−1) (T large, so Δ², ε_n² ≤ 1/4). θ̂^t_1 = w_1 has zero loss at every t. By Cauchy–Schwarz ‖ϕ(t)‖²_{(Σ^t_1)^{-1}} ≥ ε_t²/(1 + Σ_{i<t} ε_i²) = σ², so arm t has index ≥ 1 − Δ + √R σ = 1 and Q̄^t_1(t) = 1 = Q̄^t_1(0) is a maximum; the tie-break that plays arm t in episode t has Reg = TΔ = 3√(c/2)·√(T log T log(2T)), while the printed bound is C√(27 T log(2T)), and the ratio grows as √(log T). The proof on p. 137 produces the factor: it bounds Reg by √R H √(dT log(1 + T/d)) and drops the second logarithm in the final rate
--   - reading: "R = c · d² log(HT/δ) for a sufficiently large numerical constant c", Reg ≲ … → ∃ c₀ > 0, ∀ c ≥ c₀, ∃ C, and Reg ≤ C·H√(d³T log(HT/δ) log(1 + T/d)) with C depending only on c; reason: "sufficiently large" means every c above a threshold; the constant of ≲ may depend on the numerical c and on nothing else
--   - encoding: f^M(π_M) with π_M ∈ arg max_{π∈Π_rns} f^M(π) → E_{s₁∼d₁}[V^{M,⋆}_1(s₁)] with V^{M,⋆} from the Bellman optimality recursion (EpisodicMDP.optValue); reason: equal to max_π f^M(π) by Proposition 25 (p. 83), and defined even when no optimal policy is attained
--   - encoding: "with probability at least 1 − δ" → the outer measure of the bad event is at most δ; reason: equivalent when the event is measurable; no measurability of the selections is needed
--   - encoding: LSVI-UCB interacting with M (algorithm box, p. 133; episode protocol, p. 81) → a run on a filtered probability space (IsLSVIUCBRun): policies and estimates fixed before each episode, s^t_1 ∼ d₁, s^t_{h+1} ∼ P^M_h, r^t_h ∼ R^M_h given the past, and the algorithm's computations along every realization (IsLSVITrace); reason: the standard formal model of the interaction; the conditional laws are stated through conditional expectations of indicators
--   - generalization: r_h ∼ R^M_h(s_h, a_h) and s_{h+1} ∼ P^M_h(s_h, a_h) (p. 81) → each with its conditional law given the past; their joint law is left free; reason: the book's process is one such coupling, so the statement specializes to it
--   - encoding: θ̂^t_h = arg min, π̂^t_h(s) = arg max, with no tie-breaking rule; max_a Q̄^t_{h+1}(s', a) in the regression target → any minimizer over the closed ball B(ρ) and any maximizer, chosen by the run; ⨆_a Q̄^t_{h+1}(s', a); reason: every tie-breaking rule is covered; Q̄^t_{h+1} is bounded, so ⨆ is the maximum whenever it exists
--   - reading: "both cumulative and individual-step rewards are in [0, 1]" (pp. 129, 132), with no statement of where the cumulative bound holds → the cumulative bound holds from every state at every layer (IsLowRank.cumulative); reason: the proof of Lemma 28 (p. 137) uses Q^{M,⋆}_h ≤ 1 at every (s, a, h); read from the initial distribution only, this can fail at states d₁ never reaches
--   - generalization: Σ_h r_h ∈ [0, 1] almost surely → Q^{M,⋆}_h(s, a) ≤ 1 for every h ∈ [H] and (s, a); reason: Q^{M,⋆}_h is the largest expected reward-to-go, so the almost-sure bound implies it; only this consequence is used
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 46, (7.8), p. 134; proof pp. 134–137

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
import Definitions.Def_FoundationsRL_LSVI_IsLowRank
import Definitions.Def_FoundationsRL_LSVI_IsLSVITrace
import Definitions.Def_FoundationsRL_LSVI_IsLSVIUCBRun

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LSVI

universe u v w

/-- **Proposition 46** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, Proposition 46, (7.8), p. 134): regret of LSVI-UCB in
low-rank MDPs. There is a numerical constant `c₀` such that for every `c ≥ c₀` there is a
constant `C` with the following property. For every low-rank MDP `M` with features
`ϕ : S × A → ℝ^d`, horizon `H` and `T` episodes with `HT ≥ 2`, and every `δ > 0`, LSVI-UCB run
with `R = c · d² log(HT/δ)` and `ρ = 2√d` has, with probability at least `1 − δ`,
`Reg = Σ_{t=1}^T f^M(π_M) − f^M(π̂^t) ≤ C · H √(d³ T log(HT/δ) log(1 + T/d))`.

**Formalization Note.** "For a sufficiently large numerical constant `c`" is `∃ c₀, ∀ c ≥ c₀`;
the constant of `≲` may depend on `c` but on nothing else. `f^M(π_M)` is
`E_{s₁∼d₁} V^{M,⋆}_1(s₁)`. The probability of the bad event is bounded through the outer
measure, so no measurability of the regret is required. The hypothesis `HT ≥ 2` and the factor
`log(1 + T/d)` correct the printed proposition, whose rate has no such factor although its proof
(p. 137) produces it (see the item's differences). -/
theorem proposition_46 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ,
      ∀ {S : Type u} {A : Type v} [Countable S] {d H T : ℕ} (M : EpisodicMDP S A)
        (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
        {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (st : ℕ → ℕ → Ω → S) (rw : ℕ → ℕ → Ω → ℝ)
        (θhat : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (pol : ℕ → ℕ → S → Ω → A),
        IsLowRank M H ϕ → 2 ≤ H * T → 0 < δ →
        IsLSVIUCBRun M ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) (2 * Real.sqrt d) H T
          μ 𝓕 st rw θhat pol →
        μ {ω | C * H * Real.sqrt ((d : ℝ) ^ 3 * T * Real.log ((H : ℝ) * T / δ) *
              Real.log (1 + (T : ℝ) / d)) <
            regret M H T (fun t h x => pol t h x ω)} ≤ ENNReal.ofReal δ := by sorry

end FoundationsRL.LSVI
