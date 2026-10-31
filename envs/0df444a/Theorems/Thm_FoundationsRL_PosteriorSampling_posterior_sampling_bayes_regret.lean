-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_posterior_sampling_bayes_regret
-- name    : FoundationsRL.PosteriorSampling.posterior_sampling_bayes_regret
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:33.201359+00:00
-- url     : https://prove2.me/theorems/3503bd94-75c6-4357-9860-b83ac85cee5c
-- title:
--   Proposition 6, p. 31 — posterior sampling has Bayesian regret at most $\sqrt{AT\log A}$ (corrected: rewards in $[0,1]$)
-- statement:
--   Let $\mu$ be any prior on bandit models with $A\ge1$ decisions and rewards in $[0,1]$. Let $\pi^\star$ be a measurable selection of the optimal decision of the model $M^\star\sim\mu$. For every $T$, the posterior sampling algorithm, which plays $\pi^t\sim p^t=\mathbb P(\pi^\star=\cdot\mid H^{t-1})$, satisfies
--
--   $$
--   \mathrm{Reg}_{\mathsf{Bayes}}(\mu)\le\sqrt{AT\log A}.
--   $$
--
--   The bound holds for every prior, with no structure on the reward distributions, and has no dependence on the number of models. It is the Bayesian counterpart of the regret of the upper confidence bound algorithm.
--
--   Differences from the source:
--   - correction: rewards rᵗ ∈ ℝ with no range (p. 21) → rewards in [0, 1] almost surely under the prior (RewardsInUnitInterval); reason: the printed statement is false for unbounded rewards: A = 2, T = 1, rewards c·𝟙{π = θ}, θ uniform, give Reg_Bayes = c/2 > √(2 log 2) for c > 2.36
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: pᵗ(π) = ℙ(π⋆ = π | H^{t-1}), rounds t = 1, …, T → the almost-sure identity on the joint law of (H, π⋆) (IsPosteriorSampling), rounds t = 0, …, T − 1; reason: this is what the conditional probability means; the history at index t has t entries
--   - encoding: E_{πᵗ∼pᵗ}[f⋆(πᵗ)] inside Reg → f⋆(πᵗ) under the outer expectation of the joint law; reason: the same number, and the form the source uses on p. 35
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 6, Eq. (2.22), p. 31; full proof in §2.6, pp. 35–36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_IsPosteriorSampling
import Definitions.Def_FoundationsRL_PosteriorSampling_bayesRegret

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- Proposition 6 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, Proposition 6, Eq. (2.22), p. 31; full proof in §2.6,
pp. 35–36): for any prior `μ`, the posterior sampling algorithm ensures
`Reg_Bayes(μ) ≤ √(AT log A)`.

**Formalization Note.** Correction: rewards lie in `[0, 1]` (`RewardsInUnitInterval`). As printed, for
unbounded rewards the bound is false: with `A = 2`, `T = 1`, deterministic rewards `c·𝟙{π = θ}`
and `θ` uniform on the two arms, `Reg_Bayes = c/2 > √(2 log 2)` for `c > 2.36`. The theorem holds
for every measurable selection of `arg max f^M`. -/
theorem posterior_sampling_bayes_regret {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (hμ : RewardsInUnitInterval μ) (π : BanditPolicy A) (T : ℕ)
    (hπ : IsPosteriorSampling μ sel π T) :
    bayesRegret μ sel π T ≤ Real.sqrt ((A : ℝ) * T * Real.log A) := by sorry

end FoundationsRL.PosteriorSampling
