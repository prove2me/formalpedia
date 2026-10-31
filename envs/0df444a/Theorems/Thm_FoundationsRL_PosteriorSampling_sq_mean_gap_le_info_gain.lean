-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_sq_mean_gap_le_info_gain
-- name    : FoundationsRL.PosteriorSampling.sq_mean_gap_le_info_gain
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:41.718983+00:00
-- url     : https://prove2.me/theorems/5f57fa6d-920b-4477-9266-2969374d6fd7
-- title:
--   Eq. (2.33), p. 36 — squared mean gap is at most the information gain (corrected: rewards in $[0,1]$)
-- statement:
--   Let $\mu$ be a prior with rewards in $[0,1]$ and let $\pi$ be the posterior sampling algorithm. At every round, almost surely in the history,
--
--   $$
--   \mathbb E_{\pi^t,\pi^\star\sim p^t}\big[(\bar f^t_{\pi^\star}(\pi^t)-\bar f^t(\pi^t))^2\big]\le\mathbb E_{t-1}\big[D_{\mathsf{KL}}(P_{r^t\mid\pi^\star,\pi^t,H^{t-1}}\,\|\,P_{r^t\mid\pi^t,H^{t-1}})\big],
--   $$
--
--   and the right side equals
--
--   $$
--   \mathbb E_{t-1}\big[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})\big].
--   $$
--
--   This says that a large squared gap between the conditional and the unconditional posterior means forces a large information gain about $\pi^\star$.
--
--   Differences from the source:
--   - correction: rewards rᵗ ∈ ℝ with no range (p. 21) → rewards in [0, 1] almost surely under the prior (RewardsInUnitInterval); reason: Pinsker's inequality needs a range: with rewards c·𝟙{π = θ}, θ uniform on two arms, the left side grows like c² and the right side stays at most log 2
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: pᵗ(π) = ℙ(π⋆ = π | H^{t-1}), rounds t = 1, …, T → the almost-sure identity on the joint law of (H, π⋆) (IsPosteriorSampling), rounds t = 0, …, T − 1; reason: this is what the conditional probability means; the history at index t has t entries
--   - encoding: E_{t-1}[·] and posterior quantities as functions of H^{t-1} → regular conditional distributions (Measure.condKernel), statement almost sure in the history; reason: conditional expectations are defined up to null sets
--   - encoding: E_{t-1}[f⋆(π) | π⋆ = a] is undefined when ℙ_{t-1}(π⋆ = a) = 0 → elementary conditioning, with value 0 on a null event; reason: such terms carry the weight pᵗ(a) = 0 in the book's formulas
--   - encoding: two equalities through P_{π⋆|πᵗ,rᵗ,H^{t-1}} → one equality; reason: H^t = (H^{t-1}, πᵗ, rᵗ), so P_{π⋆|πᵗ,rᵗ,H^{t-1}} and P_{π⋆|H^t} are the same term
--   - encoding: D_KL as a real quantity → InformationTheory.klDiv in ℝ≥0∞, with finiteness stated and ENNReal.toReal for the real value; reason: Lean convention; the same numbers
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (2.33) and the display before it, p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_IsPosteriorSampling
import Definitions.Def_FoundationsRL_PosteriorSampling_infoGain

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- The squared mean gap is at most the information gain about `π⋆` (Foster & Rakhlin,
*Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1,
Eq. (2.33) and the display before it, p. 36):
`E_{πᵗ,π⋆∼pᵗ}[(f̄ᵗ_{π⋆}(πᵗ) − f̄ᵗ(πᵗ))²] ≤ E_{t-1}[D_KL(P_{r|π⋆,π,H^{t-1}} ∥ P_{r|π,H^{t-1}})]
 = E_{t-1}[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})]`.

**Formalization Note.** Almost sure in the history. The left side is nonnegative and is embedded
in `ℝ≥0∞` by `ENNReal.ofReal`. The book's intermediate term with `P_{π⋆|πᵗ,rᵗ,H^{t-1}}` is the
same Lean term as the last one, since `H^t` is `appendRound`. Correction: rewards lie in
`[0, 1]` (`RewardsInUnitInterval`). The step is Pinsker's inequality, and without a range it fails:
with rewards `c·𝟙{π = θ}`, `θ` uniform on two arms and `c` large, the left side grows like `c²`
while the right side stays at most `log 2`. With the range the proof gives the stronger constant
`1/2`; the constant `1` stated here is the book's. -/
theorem sq_mean_gap_le_info_gain {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (hμ : RewardsInUnitInterval μ) (π : BanditPolicy A) (T : ℕ)
    (hπ : IsPosteriorSampling μ sel π T) (t : ℕ) (ht : t < T) :
    ∀ᵐ h ∂histLaw μ π t,
      ENNReal.ofReal (∑ a, ∑ a', (π.select t h {a}).toReal * (π.select t h {a'}).toReal *
          (postMeanGiven μ sel π t h a' a - postMean μ sel π t h a) ^ 2) ≤
        rewardInfoGain μ sel π t h ∧
      rewardInfoGain μ sel π t h = posteriorInfoGain μ sel π t h := by sorry

end FoundationsRL.PosteriorSampling
