-- Prove2me | Theorems.Thm_FoundationsRL_LSVI_lemma_28
-- name    : FoundationsRL.LSVI.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:08.751933+00:00
-- url     : https://prove2.me/theorems/dd11b841-4732-4f1d-b78f-f1265f6d1b00
-- title:
--   Lemma 28, p. 136 — pointwise error bound (7.13) and optimism (7.14) of LSVI-UCB (corrected: $HT\ge2$)
-- statement:
--   For every constant $C_1$ there is a numerical constant $c_0>0$ such that the following holds for every $c\ge c_0$. Run LSVI-UCB with $\rho=2\sqrt d$ and $R=c\cdot d^2\log(HT/\delta)$ in a low-rank MDP, with $HT\ge2$ and $\delta\in(0,1)$, and suppose the event of Lemma 27 occurs with constant $C_1$:
--   $$
--   \sum_{i<t}\Big(\hat Q^t_h(s^i_h,a^i_h)-\big[\mathcal T^M_h\bar Q^t_{h+1}\big](s^i_h,a^i_h)\Big)^2\le C_1\,d^2\log(HT/\delta)\quad\text{for all }t\in[T],\ h\in[H].
--   $$
--   Then for all $t\in[T]$, $h\in[H]$ and all $(s,a)$:
--
--   1. the estimate is accurate wherever $\phi(s,a)$ is covered by the data,
--   $$
--   \Big|\hat Q^t_h(s,a)-\big[\mathcal T^M_h\bar Q^t_{h+1}\big](s,a)\Big|\le\sqrt{c_0\,d^2\log(HT/\delta)}\;\|\phi(s,a)\|_{(\Sigma^t_h)^{-1}};\tag{7.13}
--   $$
--   2. the optimistic estimate is optimistic,
--   $$
--   \bar Q^t_h(s,a)\ge Q^{M,\star}_h(s,a).\tag{7.14}
--   $$
--
--   Optimism reduces the regret of each episode to a sum of Bellman residuals of $\bar Q^t$ along the played trajectory, and (7.13) bounds these residuals by the elliptic bonuses.
--
--   Differences from the source:
--   - encoding: state space S, transitions summed as Σ_{s'} (p. 132), A large or infinite → S a countable type with P^M_h(· | s, a) a probability mass function; A an arbitrary type; reason: the book's Σ_{s'} presupposes a countable S; no finiteness is assumed
--   - correction: no condition on H and T → HT ≥ 2; reason: the printed lemma is false at H = T = 1: H = T = 1, d = 2, one state s₀, actions a₁, a₂ with ϕ(a₁) = e₁, ϕ(a₂) = e₂, μ_1(s₀) = (1, 1), w_1 = (0, 1/2), deterministic rewards; θ̂^1_1 = (1, 0) minimizes the empty objective over B(2√2), so Q̄^1_1(a₁) = 1 > Q̄^1_1(a₂) = √R and the greedy action a₁ has regret 1/2, while log(HT/δ) = log(1/δ) → 0 as δ ↑ 1; the event of Lemma 27 holds (all sums are empty), yet |Q̂^1_1(a₁) − T Q̄^1_2(a₁)| = 1 exceeds √(c₀·4·log(1/δ)) → 0, and Q̄^1_1(a₂) = √R → 0 < 1/2 = Q^{M,⋆}_1(a₂)
--   - reading: δ unconstrained (inherited from "with probability at least 1 − δ" in Lemma 27) → δ ∈ (0, 1); reason: the usual range of a confidence parameter; for δ ≥ HT the bonus vanishes and the lemma is false
--   - reading: ≲ in (7.13), bonus b^t_{h,δ} identified with the algorithm's √R ‖ϕ‖_{(Σ^t_h)^{-1}} → for every event constant C₁ there is c₀ > 0 with (7.13) holding with constant √c₀, and (7.14) holding whenever c ≥ c₀; reason: (7.14) needs the algorithm's bonus to dominate the right side of (7.13), which is the "sufficiently large c" of Proposition 46
--   - encoding: "whenever the event in Lemma 27 occurs" → a deterministic statement: for every realization of the algorithm's computations (IsLSVITrace) on which the inequality of Lemma 27 holds with constant C₁; reason: the lemma uses nothing about the realization but the event
--   - reading: "both cumulative and individual-step rewards are in [0, 1]" (pp. 129, 132), with no statement of where the cumulative bound holds → the cumulative bound holds from every state at every layer (IsLowRank.cumulative); reason: the proof of Lemma 28 (p. 137) uses Q^{M,⋆}_h ≤ 1 at every (s, a, h); read from the initial distribution only, this can fail at states d₁ never reaches
--   - generalization: Σ_h r_h ∈ [0, 1] almost surely → Q^{M,⋆}_h(s, a) ≤ 1 for every h ∈ [H] and (s, a); reason: Q^{M,⋆}_h is the largest expected reward-to-go, so the almost-sure bound implies it; only this consequence is used
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 28, (7.13)–(7.14), p. 136, proof pp. 136–137

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
import Definitions.Def_FoundationsRL_LSVI_IsLowRank
import Definitions.Def_FoundationsRL_LSVI_IsLSVITrace

open MeasureTheory

namespace FoundationsRL.LSVI

universe u v

/-- **Lemma 28** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Lemma 28, (7.13)–(7.14), p. 136): pointwise error and optimism of
LSVI-UCB. For every constant `C₁` (the constant of the event of Lemma 27) there is a numerical
constant `c₀ > 0` such that the following holds whenever `c ≥ c₀`. Run LSVI-UCB with
`ρ = 2√d` and `R = c · d² log(HT/δ)` in a low-rank MDP, `HT ≥ 2`, `δ ∈ (0, 1)`, and suppose the
event of Lemma 27 occurs: `Σ_{i<t} (Q̂^t_h(s^i_h, a^i_h) − [T^M_h Q̄^t_{h+1}](s^i_h, a^i_h))² ≤
C₁ d² log(HT/δ)` for all `t ∈ [T]`, `h ∈ [H]`. Then for all `t ∈ [T]`, `h ∈ [H]` and `(s, a)`:

1. (7.13) `|Q̂^t_h(s, a) − [T^M_h Q̄^t_{h+1}](s, a)| ≤ √(c₀ d² log(HT/δ)) · ‖ϕ(s, a)‖_{(Σ^t_h)^{-1}}`;
2. (7.14) `Q̄^t_h(s, a) ≥ Q^{M,⋆}_h(s, a)`.

**Formalization Note.** The statement is deterministic: it holds along every realization of the
algorithm's computations (`IsLSVITrace`) on which the event occurs. The book's `≲` in (7.13)
is the constant `c₀`, and the bonus `√R ‖ϕ‖_{(Σ^t_h)^{-1}}` of the algorithm dominates the right
side of (7.13) because `c ≥ c₀`. The hypothesis `HT ≥ 2` corrects the printed lemma (see the
item's differences). -/
theorem lemma_28 :
    ∀ C₁ : ℝ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      ∀ {S : Type u} {A : Type v} [Countable S] {d H T : ℕ} (M : EpisodicMDP S A)
        (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (s : ℕ → ℕ → S) (r : ℕ → ℕ → ℝ)
        (θhat : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (pol : ℕ → ℕ → S → A),
        IsLowRank M H ϕ → 2 ≤ H * T → 0 < δ → δ < 1 →
        IsLSVITrace ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) (2 * Real.sqrt d) H T
          s r θhat pol →
        (∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H,
          ∑ i ∈ Finset.Ico 1 t,
              (inner ℝ (ϕ (s i h) (pol i h (s i h))) (θhat t h) -
                M.bellman h
                  (Qbar ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) H s
                    (fun j k => pol j k (s j k)) θhat t (h + 1))
                  (s i h) (pol i h (s i h))) ^ 2
            ≤ C₁ * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) →
        ∀ t ∈ Finset.Icc 1 T, ∀ h ∈ Finset.Icc 1 H, ∀ x b,
          |inner ℝ (ϕ x b) (θhat t h) -
              M.bellman h
                (Qbar ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) H s
                  (fun j k => pol j k (s j k)) θhat t (h + 1)) x b| ≤
            Real.sqrt (c₀ * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) *
              ellNorm (gram ϕ s (fun j k => pol j k (s j k)) t h) (ϕ x b) ∧
          M.Qstar H h x b ≤
            Qbar ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) H s
              (fun j k => pol j k (s j k)) θhat t h x b := by sorry

end FoundationsRL.LSVI
