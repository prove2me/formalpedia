-- Prove2me | Theorems.Thm_FoundationsRL_PosteriorSampling_kl_symmetry
-- name    : FoundationsRL.PosteriorSampling.kl_symmetry
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:41.612401+00:00
-- url     : https://prove2.me/theorems/6f86dd3a-1b49-49de-9fd9-77cf50b0f978
-- title:
--   §2.6, p. 36 — symmetry of the expected KL divergence
-- statement:
--   For a pair $(X,Y)$ of random variables,
--
--   $$
--   \mathbb E_X\big[D_{\mathsf{KL}}(P_{Y\mid X}\,\|\,P_Y)\big]=\mathbb E_Y\big[D_{\mathsf{KL}}(P_{X\mid Y}\,\|\,P_X)\big].
--   $$
--
--   Both sides are the mutual information between $X$ and $Y$. The identity turns information carried by the reward about $\pi^\star$ into the change of the posterior of $\pi^\star$.
--
--   **Formalization Note** The conditional laws are regular conditional distributions, and both sides take values in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: random variables X, Y, no space specified → values in standard Borel spaces; reason: this is where P_{Y|X} and P_{X|Y} exist as conditional laws
--   - encoding: D_KL as a real quantity → InformationTheory.klDiv in ℝ≥0∞; reason: both sides may be infinite
--   - encoding: X, Y random variables (their value spaces carry a law) → [Nonempty X] [Nonempty Y]; reason: a probability measure on X × Y already forces both spaces nonempty; the instances are needed by Measure.condKernel and exclude no instance
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §2.6, line before (2.33), p. 36

import Mathlib

open MeasureTheory ProbabilityTheory InformationTheory

namespace FoundationsRL.PosteriorSampling

/-- Symmetry of the expected KL divergence (Foster & Rakhlin, *Foundations of Reinforcement
Learning and Interactive Decision Making*, arXiv:2312.16730v1, §2.6, p. 36):
`E_X[D_KL(P_{Y|X} ∥ P_Y)] = E_Y[D_KL(P_{X|Y} ∥ P_X)]`, for a pair `(X, Y)` of law `ρ`.

**Formalization Note.** `X` and `Y` take values in standard Borel spaces, where the conditional
laws `P_{Y|X}` and `P_{X|Y}` exist as kernels (`Measure.condKernel`). Both sides are in `ℝ≥0∞`
and may be `∞`. -/
theorem kl_symmetry {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] :
    ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst =
      ∫⁻ y, klDiv ((ρ.map Prod.swap).condKernel y) ρ.fst ∂ρ.snd := by sorry

end FoundationsRL.PosteriorSampling
