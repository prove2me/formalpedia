-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_decoupling_posterior_means
-- name    : FoundationsRL.PosteriorSampling.decoupling_posterior_means
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:20.937989+00:00
-- url     : https://prove2.me/theorems/ddc3aa71-23fa-4046-a8be-555ed22d027d
-- title:
--   Eq. (2.32), p. 36 — decoupling applied to the posterior means
-- statement:
--   For a decision distribution $p^t$ and the posterior means $\bar f^t$, $\bar f^t_{\pi'}$,
--
--   $$
--   \mathbb E_{\pi\sim p^t}\big[\bar f^t_\pi(\pi)-\bar f^t(\pi)\big]\le\sqrt{A\cdot\mathbb E_{\pi,\pi^\star\sim p^t}\big[(\bar f^t_{\pi^\star}(\pi)-\bar f^t(\pi))^2\big]},
--   $$
--
--   where $\pi$ and $\pi^\star$ are drawn independently from $p^t$.
--
--   On the left, the two indices of $\bar f^t_\pi(\pi)$ coincide. On the right, they are drawn independently, which is what lets the bound be compared with the information gained in a round.
--
--   Differences from the source:
--   - generalization: stated for posterior sampling, for the realized history → stated for every algorithm and at every history, not only almost surely; reason: the inequality is Cauchy–Schwarz on [A] and uses nothing about p^t; the source's case is an instance
--   - reading: π⋆ := arg max_π f⋆(π), no tie-breaking rule → any measurable selection (OptimalSelection); reason: the book names no rule and the result holds for every measurable one; the minimal-index rule is an instance
--   - encoding: a prior on reward distributions M, no σ-algebra given → a probability measure on BanditModel A, the subtype of Fin A → Measure ℝ of probability measures with a mean, with the Giry σ-algebra; reason: any family of reward laws indexed by a measurable parameter space pushes forward to this type; the mean is what Eq. (2.2) presupposes
--   - encoding: E_{t-1}[f⋆(π) | π⋆ = a] is undefined when ℙ_{t-1}(π⋆ = a) = 0 → elementary conditioning, with value 0 on a null event; reason: such terms carry the weight pᵗ(a) = 0 in the book's formulas
--   - encoding: A ∈ ℕ decisions, Π = {1, …, A}; π⋆ := arg max over Π presupposes Π nonempty → [NeZero A], i.e. A ≥ 1; reason: with A = 0 the decision space is empty and π⋆ is undefined; the condition excludes only that undefined case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (2.32), p. 36

import Mathlib
import Definitions.Def_FoundationsRL_PosteriorSampling_posterior

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace FoundationsRL.PosteriorSampling

/-- The decoupling inequality for the posterior means (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (2.32), p. 36):
`E_{π∼pᵗ}[f̄ᵗ_π(π) − f̄ᵗ(π)] ≤ √(A · E_{π,π⋆∼pᵗ}[(f̄ᵗ_{π⋆}(π) − f̄ᵗ(π))²])`, with `π` and `π⋆` drawn
independently from `pᵗ`.

**Formalization Note.** The inequality holds at every history and for every decision
distribution `pᵗ = π.select t h`: only Cauchy–Schwarz on `[A]` is involved, so neither an
almost-sure qualifier nor the posterior sampling hypothesis is needed. -/
theorem decoupling_posterior_means {A : ℕ} [NeZero A]
    (μ : Measure (BanditModel A)) [IsProbabilityMeasure μ] (sel : OptimalSelection A)
    (π : BanditPolicy A) (t : ℕ) (h : BanditHistory A t) :
    ∑ a, (π.select t h {a}).toReal *
        (postMeanGiven μ sel π t h a a - postMean μ sel π t h a) ≤
      Real.sqrt ((A : ℝ) * ∑ a, ∑ a', (π.select t h {a}).toReal * (π.select t h {a'}).toReal *
        (postMeanGiven μ sel π t h a' a - postMean μ sel π t h a) ^ 2) := by sorry

end FoundationsRL.PosteriorSampling
