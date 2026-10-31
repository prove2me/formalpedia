-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_sum_infoGain_le_log
-- name    : FoundationsRL.PosteriorSampling.sum_infoGain_le_log
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:06.717659+00:00
-- url     : https://prove2.me/theorems/681bdbb7-e749-479b-8b67-d1c3fa0d4edc
-- title:
--   §2.6, last display, p. 36 — entropy telescoping bounds the total information gain by $\log A$
-- statement:
--   For every $T$,
--
--   $$
--   \sum_{t=1}^T\mathbb E\big[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})\big]=\mathrm{Ent}(\pi^\star\mid H^0)-\mathrm{Ent}(\pi^\star\mid H^T)\le\log A.
--   $$
--
--   The total information about $\pi^\star$ that any number of rounds can reveal is at most the entropy of $\pi^\star$, whatever the prior and the reward distributions.
--
--   Differences from the source:
--   - generalization: stated for posterior sampling → stated for every algorithm; reason: the identity and the entropy bound do not use the form of the algorithm; posterior sampling is an instance
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: D_KL as a real quantity → InformationTheory.klDiv in ℝ≥0∞, with finiteness stated and ENNReal.toReal for the real value; reason: Lean convention; the same numbers
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, last display, p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_infoGain
import Definitions.Def_FoundationsRL_PosteriorSampling_condEnt

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- Entropy telescoping (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, §2.6, last display, p. 36):
`∑_{t=1}^T E[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})] = Ent(π⋆ | H^0) − Ent(π⋆ | H^T) ≤ log A`.

**Formalization Note.** The sum is finite and its real value is stated, as in
`expectedInfoGain_eq_entropy_drop`. The identity holds for every policy. -/
theorem sum_infoGain_le_log {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (π : BanditPolicy A) (T : ℕ) :
    (∑ t ∈ Finset.range T, expectedInfoGain μ sel π t) ≠ ⊤ ∧
      (∑ t ∈ Finset.range T, expectedInfoGain μ sel π t).toReal =
        condEnt μ sel π 0 - condEnt μ sel π T ∧
      condEnt μ sel π 0 - condEnt μ sel π T ≤ Real.log A := by sorry

end FoundationsRL.PosteriorSampling
