-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_bayesRegret_eq_sum_round
-- name    : FoundationsRL.PosteriorSampling.bayesRegret_eq_sum_round
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:53.670335+00:00
-- url     : https://prove2.me/theorems/0026beca-b4a2-42ae-b93f-03c077b6c1ca
-- title:
--   §2.6, first display, p. 35 — law of total expectation for the Bayesian regret
-- statement:
--   Let $\mu$ be a prior on bandit models whose mean rewards are integrable, $\pi^\star$ a measurable selection of the optimal decision, and $\pi$ an algorithm. Then
--
--   $$
--   \mathrm{Reg}_{\mathsf{Bayes}}(\mu)=\mathbb E\Big[\sum_{t=1}^T\mathbb E_{t-1}\big[f^\star(\pi^\star)-f^\star(\pi^t)\big]\Big].
--   $$
--
--   This reduces the analysis to a single round.
--
--   Differences from the source:
--   - generalization: stated for posterior sampling → stated for every algorithm; reason: the identity is the tower property and does not use the form of the algorithm; posterior sampling is an instance
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: expectations of f⋆ are written without comment → the hypothesis that each f⋆(a) is integrable under the prior; reason: the expectations must exist for the display to have a meaning; bounded rewards imply it
--   - encoding: E_{t-1}[·] and posterior quantities as functions of H^{t-1} → regular conditional distributions (Measure.condKernel), statement almost sure in the history; reason: conditional expectations are defined up to null sets
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, first display, p. 35

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_bayesRegret
import Definitions.Def_FoundationsRL_PosteriorSampling_roundLaw

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- Law of total expectation for the Bayesian regret (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, first display,
p. 35): `Reg_Bayes(μ) = E[∑_{t=1}^T E_{t-1}[f⋆(π⋆) − f⋆(πᵗ)]]`, the inner conditional expectation
being the integral against `roundLaw`.

**Formalization Note.** The identity uses neither the optimality of `π⋆` nor the form of the
algorithm, so it is stated for every policy. `hint` says that the expectations exist; bounded
rewards imply it. -/
theorem bayesRegret_eq_sum_round {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (hint : ∀ a, Integrable (fun M => meanReward M a) μ) (π : BanditPolicy A) (T : ℕ) :
    bayesRegret μ sel π T =
      ∑ t : Fin T, ∫ h, (∫ z, (z.2.2.2 z.2.2.1 - z.2.2.2 z.1) ∂roundLaw μ sel π t h)
        ∂histLaw μ π t := by sorry

end FoundationsRL.PosteriorSampling
