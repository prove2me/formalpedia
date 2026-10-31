-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_round_regret_eq_posterior_means
-- name    : FoundationsRL.PosteriorSampling.round_regret_eq_posterior_means
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:57.549814+00:00
-- url     : https://prove2.me/theorems/c9efbf63-a737-4f40-aef3-64120451fc4d
-- title:
--   §2.6, display before (2.32), p. 36 — regret per round in terms of the posterior means
-- statement:
--   Let $\mu$ be a prior whose mean rewards are integrable and let $\pi$ be the posterior sampling algorithm. At every round, almost surely in the history,
--
--   $$
--   \mathbb E_{t-1}\big[f^\star(\pi^\star)-f^\star(\pi^t)\big]=\mathbb E_{\pi\sim p^t}\big[\bar f^t_\pi(\pi)-\bar f^t(\pi)\big].
--   $$
--
--   The left side couples the optimal decision to the model. The right side involves only the posterior means and the decision distribution.
--
--   Differences from the source:
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: pᵗ(π) = ℙ(π⋆ = π | H^{t-1}), rounds t = 1, …, T → the almost-sure identity on the joint law of (H, π⋆) (IsPosteriorSampling), rounds t = 0, …, T − 1; reason: this is what the conditional probability means; the history at index t has t entries
--   - encoding: expectations of f⋆ are written without comment → the hypothesis that each f⋆(a) is integrable under the prior; reason: the expectations must exist for the display to have a meaning; bounded rewards imply it
--   - encoding: E_{t-1}[·] and posterior quantities as functions of H^{t-1} → regular conditional distributions (Measure.condKernel), statement almost sure in the history; reason: conditional expectations are defined up to null sets
--   - encoding: E_{t-1}[f⋆(π) | π⋆ = a] is undefined when ℙ_{t-1}(π⋆ = a) = 0 → elementary conditioning, with value 0 on a null event; reason: such terms carry the weight pᵗ(a) = 0 in the book's formulas
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, display before (2.32), p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_IsPosteriorSampling
import Definitions.Def_FoundationsRL_PosteriorSampling_posterior
import Definitions.Def_FoundationsRL_PosteriorSampling_roundLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- Regret per round in terms of the posterior means (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, display before
(2.32), p. 36): `E_{t-1}[f⋆(π⋆) − f⋆(πᵗ)] = E_{π∼pᵗ}[f̄ᵗ_π(π) − f̄ᵗ(π)]`.

**Formalization Note.** Almost sure in the history, as every statement about conditional
expectations is. `(π.select t h {a}).toReal` is `pᵗ(a)`. `hint` says that the expectations exist. -/
theorem round_regret_eq_posterior_means {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (hint : ∀ a, Integrable (fun M => meanReward M a) μ) (π : BanditPolicy A) (T : ℕ) (hπ : IsPosteriorSampling μ sel π T) (t : ℕ) (ht : t < T) :
    ∀ᵐ h ∂histLaw μ π t,
      ∫ z, (z.2.2.2 z.2.2.1 - z.2.2.2 z.1) ∂roundLaw μ sel π t h =
        ∑ a, (π.select t h {a}).toReal *
          (postMeanGiven μ sel π t h a a - postMean μ sel π t h a) := by sorry

end FoundationsRL.PosteriorSampling
