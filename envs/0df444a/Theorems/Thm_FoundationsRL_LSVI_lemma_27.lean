-- Prove2me | Theorems.Thm_FoundationsRL_LSVI_lemma_27
-- name    : FoundationsRL.LSVI.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:57.811328+00:00
-- url     : https://prove2.me/theorems/f3bfc467-c177-45c6-a2f9-88d2c6c741c4
-- title:
--   Lemma 27, p. 135 — regression error of every layer of LSVI-UCB is $\lesssim d^2\log(HT/\delta)$
-- statement:
--   Run LSVI-UCB with $\rho=2\sqrt d$ and $R=c\cdot d^2\log(HT/\delta)$ in a low-rank MDP with features in $\mathbb R^d$, horizon $H$, for $T$ episodes. There is a numerical constant $c_0>0$ such that for every $c\ge c_0$ there is a constant $C$, independent of the MDP, $d$, $H$, $T$ and $\delta$, such that for every $\delta>0$, with probability at least $1-\delta$, for all $t\in[T]$ and $h\in[H]$,
--   $$
--   \sum_{i<t}\Big(\hat Q^t_h(s^i_h,a^i_h)-\big[\mathcal T^M_h\bar Q^t_{h+1}\big](s^i_h,a^i_h)\Big)^2\le C\,d^2\log(HT/\delta),
--   $$
--   where $\hat Q^t_h(s,a)=\langle\phi(s,a),\hat\theta^t_h\rangle$.
--
--   The regression target $\bar Q^t_{h+1}$ depends on all the data, so the in-sample error must be controlled uniformly over the class of possible targets (7.10); this is the statistical core of the regret analysis.
--
--   **Formalization Note** The data are collected adaptively, so Lemma 26, whose design points are fixed, does not apply verbatim; a proof needs a martingale (self-normalized or Freedman-type) form of it.
--
--   Differences from the source:
--   - encoding: state space S, transitions summed as Σ_{s'} (p. 132), A large or infinite → S a countable type with P^M_h(· | s, a) a probability mass function; A an arbitrary type; reason: the book's Σ_{s'} presupposes a countable S; no finiteness is assumed
--   - reading: Lemma 27, stated inside the proof of Proposition 46 with that proposition's R = c·d² log(HT/δ) and ρ = 2√d → there is c₀ > 0 such that for every c ≥ c₀ there is C with the bound for every run with R = c·d² log(HT/δ), ρ = 2√d; reason: the lemma inherits the proposition's parameters, including "sufficiently large" c; covering the class (7.10) costs a factor depending on c, which the constant may absorb
--   - encoding: "for all t and h" → t ∈ [T], h ∈ [H]; reason: the episodes and layers of the algorithm
--   - encoding: "with probability at least 1 − δ" → the outer measure of the bad event is at most δ; reason: equivalent when the event is measurable; no measurability of the selections is needed
--   - encoding: LSVI-UCB interacting with M (algorithm box, p. 133; episode protocol, p. 81) → a run on a filtered probability space (IsLSVIUCBRun): policies and estimates fixed before each episode, s^t_1 ∼ d₁, s^t_{h+1} ∼ P^M_h, r^t_h ∼ R^M_h given the past, and the algorithm's computations along every realization (IsLSVITrace); reason: the standard formal model of the interaction; the conditional laws are stated through conditional expectations of indicators
--   - generalization: r_h ∼ R^M_h(s_h, a_h) and s_{h+1} ∼ P^M_h(s_h, a_h) (p. 81) → each with its conditional law given the past; their joint law is left free; reason: the book's process is one such coupling, so the statement specializes to it
--   - encoding: θ̂^t_h = arg min, π̂^t_h(s) = arg max, with no tie-breaking rule; max_a Q̄^t_{h+1}(s', a) in the regression target → any minimizer over the closed ball B(ρ) and any maximizer, chosen by the run; ⨆_a Q̄^t_{h+1}(s', a); reason: every tie-breaking rule is covered; Q̄^t_{h+1} is bounded, so ⨆ is the maximum whenever it exists
--   - reading: "both cumulative and individual-step rewards are in [0, 1]" (pp. 129, 132), with no statement of where the cumulative bound holds → the cumulative bound holds from every state at every layer (IsLowRank.cumulative); reason: the proof of Lemma 28 (p. 137) uses Q^{M,⋆}_h ≤ 1 at every (s, a, h); read from the initial distribution only, this can fail at states d₁ never reaches
--   - generalization: Σ_h r_h ∈ [0, 1] almost surely → Q^{M,⋆}_h(s, a) ≤ 1 for every h ∈ [H] and (s, a); reason: Q^{M,⋆}_h is the largest expected reward-to-go, so the almost-sure bound implies it; only this consequence is used
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 27, (7.12), p. 135; class (7.10), p. 134; proof sketch pp. 135–136

import Mathlib
import Definitions.Def_FoundationsRL_LSVI_EpisodicMDP
import Definitions.Def_FoundationsRL_LSVI_IsLowRank
import Definitions.Def_FoundationsRL_LSVI_IsLSVITrace
import Definitions.Def_FoundationsRL_LSVI_IsLSVIUCBRun

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LSVI

universe u v w

/-- **Lemma 27** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, Lemma 27, (7.12), p. 135): the regression error of each layer of
LSVI-UCB. Run LSVI-UCB with `ρ = 2√d` and `R = c · d² log(HT/δ)` (the parameters of
Proposition 46) in a low-rank MDP. There is a numerical constant `c₀` such that for every
`c ≥ c₀` there is a constant `C` such that, for every `δ > 0`, with probability at least `1 − δ`,
for all `t ∈ [T]` and `h ∈ [H]`,
`Σ_{i<t} (Q̂^t_h(s^i_h, a^i_h) − [T^M_h Q̄^t_{h+1}](s^i_h, a^i_h))² ≤ C · d² log(HT/δ)`,
where `Q̂^t_h(s, a) = ⟨ϕ(s, a), θ̂^t_h⟩`.

**Formalization Note.** The book states Lemma 27 inside the proof of Proposition 46, whose
parameters it inherits, including "a sufficiently large numerical constant `c`" (for small `c`
optimism fails, `Q̄^t_{h+1}` can be negative and its backup can leave the ball `B(ρ)` of the
regression); the constant may depend on the numerical constant `c` of `R`, but not on
the instance (`S`, `A`, `d`, `H`, `T`, `δ`, `M`, `ϕ`, the run). The data are collected
adaptively, so Lemma 26, whose `x_i` are fixed, does not apply verbatim. -/
theorem lemma_27 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ,
      ∀ {S : Type u} {A : Type v} [Countable S]
        {d H T : ℕ} (M : EpisodicMDP S A)
        (ϕ : S → A → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
        {Ω : Type w} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (st : ℕ → ℕ → Ω → S) (rw : ℕ → ℕ → Ω → ℝ)
        (θhat : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (pol : ℕ → ℕ → S → Ω → A),
        IsLowRank M H ϕ → 0 < δ →
        IsLSVIUCBRun M ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) (2 * Real.sqrt d) H T
          μ 𝓕 st rw θhat pol →
        μ {ω | ∃ t ∈ Finset.Icc 1 T, ∃ h ∈ Finset.Icc 1 H,
            C * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ) <
              ∑ i ∈ Finset.Ico 1 t,
                (inner ℝ (ϕ (st i h ω) (pol i h (st i h ω) ω)) (θhat t h ω) -
                  M.bellman h
                    (Qbar ϕ (c * (d : ℝ) ^ 2 * Real.log ((H : ℝ) * T / δ)) H
                      (fun j k => st j k ω) (fun j k => pol j k (st j k ω) ω)
                      (fun j k => θhat j k ω) t (h + 1))
                    (st i h ω) (pol i h (st i h ω) ω)) ^ 2}
          ≤ ENNReal.ofReal δ := by sorry

end FoundationsRL.LSVI
