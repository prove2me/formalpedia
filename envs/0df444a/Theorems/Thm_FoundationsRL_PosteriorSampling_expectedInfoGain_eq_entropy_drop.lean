-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_expectedInfoGain_eq_entropy_drop
-- name    : FoundationsRL.PosteriorSampling.expectedInfoGain_eq_entropy_drop
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:57.75969+00:00
-- url     : https://prove2.me/theorems/24d20066-bb73-4370-ab63-6550a60ff268
-- title:
--   §2.6, p. 36 — the information gain is the entropy drop
-- statement:
--   For every round,
--
--   $$
--   \mathbb E\big[D_{\mathsf{KL}}(P_{\pi^\star\mid H^t}\,\|\,P_{\pi^\star\mid H^{t-1}})\big]=\mathrm{Ent}(\pi^\star\mid H^{t-1})-\mathrm{Ent}(\pi^\star\mid H^t).
--   $$
--
--   In particular the left side is finite and the entropy of $\pi^\star$ given the history does not increase on average.
--
--   Differences from the source:
--   - generalization: stated for posterior sampling → stated for every algorithm; reason: the identity is the tower property of the posteriors of π⋆; posterior sampling is an instance
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: D_KL as a real quantity → InformationTheory.klDiv in ℝ≥0∞, with finiteness stated and ENNReal.toReal for the real value; reason: Lean convention; the same numbers
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_infoGain
import Definitions.Def_FoundationsRL_PosteriorSampling_condEnt

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- The information gain is the entropy drop (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, p. 36):
`E[D_KL(P_{π⋆|H^t} ∥ P_{π⋆|H^{t-1}})] = Ent(π⋆ | H^{t-1}) − Ent(π⋆ | H^t)`.

**Formalization Note.** The identity uses only the tower property of the posteriors of `π⋆`, so
it is stated for every policy. The gain is in `ℝ≥0∞`; the statement says it is finite and that
its real value is the difference, which also makes the difference nonnegative. Here `t` counts
completed rounds, so `H^t` of the book is `t + 1` here. -/
theorem expectedInfoGain_eq_entropy_drop {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (π : BanditPolicy A) (t : ℕ) :
    expectedInfoGain μ sel π t ≠ ⊤ ∧
      (expectedInfoGain μ sel π t).toReal = condEnt μ sel π t - condEnt μ sel π (t + 1) := by sorry

end FoundationsRL.PosteriorSampling
