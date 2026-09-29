-- Prove2me | Theorems.Thm_HighDimStat_UniformLaws_concentration_around_mean
-- name    : HighDimStat.UniformLaws.concentration_around_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:59.459984+00:00
-- url     : https://prove2.me/theorems/b6a7a3ac-7e3e-4ce7-a434-a91afe26e603
-- title:
--   Eq. (4.16) -- concentration of the empirical process around its mean
-- statement:
--   **Eq. (4.16)** (concentration around the mean, via bounded differences). For a
--   $b$-uniformly bounded function class $F$ and an i.i.d. sample $X_1,\dots,X_n$,
--
--   $$
--   \|\mathbb P_n-P\|_F - \mathbb E[\|\mathbb P_n-P\|_F] \;\le\; t
--   $$
--
--   with $P$-probability at least $1-e^{-nt^2/2b^2}$, for all $t\ge0$.
--
--   This is the first of the two halves of Theorem 4.10's proof: concentration of the empirical
--   process around its own mean, obtained via the bounded-differences method (Corollary 2.21,
--   already faithfully covered elsewhere on the platform and reused there, not redrafted here).
--   The second half — bounding the mean itself by $2R_n(F)$ via symmetrization — is
--   Proposition 4.11's content specialized to $\Phi(t)=t$.
--
--   **Formalization Note** The $b$-uniform-boundedness hypothesis is kept explicit (it is what
--   licenses the bounded-differences argument's Lipschitz constant $2b/n$ per coordinate,
--   Eq. (4.15)); dropping it would be easy to do by accident but changes the theorem, per this
--   chapter's named pitfall.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 106 (PDF p. 126), Eq. (4.16)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_IsUniformlyBounded

open MeasureTheory ProbabilityTheory

namespace HighDimStat.UniformLaws

/-- **Eq. (4.16)** (concentration of the empirical process around its mean), Wainwright,
*High-Dimensional Statistics* (2019), p. 106, established via the bounded-differences method
(Corollary 2.21) inside the proof of Theorem 4.10. For a `b`-uniformly bounded, i.i.d.-sampled
function class, `‖Pₙ-P‖_F - E[‖Pₙ-P‖_F] ≤ t` with `P`-probability at least
`1-exp(-nt²/2b²)`, for all `t≥0`. A hypothesis `hf` that each `f j` is measurable guards the
outer Bochner integral against Mathlib's junk value on a non-integrable/non-measurable function. -/
theorem concentration_around_mean {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (b : ℝ) (hb : IsUniformlyBounded f b)
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (hIndep : iIndepFun Xs Prob)
    (hIdent : ∀ i, IdentDistrib (Xs i) X0 Prob Prob) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    Prob.real {ω | empProcessDeviation f Xs X0 Prob n ω -
      ∫ ω', empProcessDeviation f Xs X0 Prob n ω' ∂Prob ≤ t} ≥
      1 - Real.exp (-((n : ℝ) * t ^ 2) / (2 * b ^ 2)) := by sorry

end HighDimStat.UniformLaws
