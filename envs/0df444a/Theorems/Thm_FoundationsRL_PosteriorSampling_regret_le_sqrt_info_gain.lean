-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_regret_le_sqrt_info_gain
-- name    : FoundationsRL.PosteriorSampling.regret_le_sqrt_info_gain
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:00.59328+00:00
-- url     : https://prove2.me/theorems/ca4ddbd8-cade-40e6-a1ab-29bc38e55465
-- title:
--   §2.6, chain after (2.33), p. 36 — regret is at most $\sqrt{AT\cdot\text{total information gain}}$ (corrected: rewards in $[0,1]$)
-- statement:
--   Let $\mu$ be a prior with rewards in $[0,1]$ and let $\pi$ be the posterior sampling algorithm. Then
--
--   $$
--   \mathrm{Reg}_{\mathsf{Bayes}}(\mu)\le\sqrt{AT\cdot\sum_{t=1}^T\mathbb E\big[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})\big]}.
--   $$
--
--   This combines (2.32), (2.33), the regret identity and the Cauchy–Schwarz inequality over the rounds.
--
--   Differences from the source:
--   - correction: rewards rᵗ ∈ ℝ with no range (p. 21) → rewards in [0, 1] almost surely under the prior (RewardsInUnitInterval); reason: the step uses (2.33), which fails without a range; for unbounded rewards this bound is false by the counterexample of Proposition 6, where the information gain is at most log 2
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: pᵗ(π) = ℙ(π⋆ = π | H^{t-1}), rounds t = 1, …, T → the almost-sure identity on the joint law of (H, π⋆) (IsPosteriorSampling), rounds t = 0, …, T − 1; reason: this is what the conditional probability means; the history at index t has t entries
--   - encoding: Reg_Bayes, the left side of the chain, which starts from the sum of E_{π∼p^t}[…] → Reg_Bayes itself; reason: the two are equal by the two preceding displays of the proof
--   - encoding: D_KL as a real quantity → InformationTheory.klDiv in ℝ≥0∞, with finiteness stated and ENNReal.toReal for the real value; reason: Lean convention; the same numbers
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, chain of displays after (2.33), p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_IsPosteriorSampling
import Definitions.Def_FoundationsRL_PosteriorSampling_bayesRegret
import Definitions.Def_FoundationsRL_PosteriorSampling_infoGain

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- The regret bound in terms of the total information gain (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, the chain of
displays after (2.33), p. 36):
`Reg_Bayes(μ) ≤ √(AT · ∑_{t=1}^T E[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})])`.

**Formalization Note.** The total information gain is finite (`sum_infoGain_le_log`), so
`ENNReal.toReal` loses nothing. Rewards are in `[0, 1]` because the step uses (2.33). -/
theorem regret_le_sqrt_info_gain {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (hμ : RewardsInUnitInterval μ) (π : BanditPolicy A) (T : ℕ)
    (hπ : IsPosteriorSampling μ sel π T) :
    bayesRegret μ sel π T ≤
      Real.sqrt ((A : ℝ) * T *
        (∑ t ∈ Finset.range T, expectedInfoGain μ sel π t).toReal) := by sorry

end FoundationsRL.PosteriorSampling
