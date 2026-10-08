-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_nthMoment_mono_of_usualOrder
-- name    : LariviereIGFR.Moments.nthMoment_mono_of_usualOrder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:18.324022+00:00
-- url     : https://prove2.me/theorems/a219fc46-3396-4f9e-8504-18e955c3ee39
-- title:
--   Proof of Theorem 2, p. 603 — X₁ ≤st X₂ with X₁, X₂ ≥ 0 ⇒ E[X₁ⁿ] ≤ E[X₂ⁿ]
-- statement:
--   Let $X_1$ and $X_2$ be nonnegative random variables with laws $\nu_1,\nu_2$, and suppose $X_1$ is stochastically smaller than $X_2$, i.e. $\mathbb P(X_1>x)\le\mathbb P(X_2>x)$ for every real $x$. Then for every real $n>0$,
--   $$
--   \mathbb E[X_1^n]\le\mathbb E[X_2^n]\qquad(\text{in }[0,\infty]).
--   $$
--
--   In the paper this carries finiteness of the Pareto moment over to $X_y$ ("Because the $n$th moment of the Pareto is finite, the $n$th moment of $X_y$ is also finite"), and infiniteness of a Pareto moment over to $X_z$ in the converse.
--
--   **Formalization Note** Both laws are required to put no mass on $(-\infty,0)$: with negative values allowed, $x\mapsto x^n$ is not monotone and the conclusion fails. Moments take values in $[0,\infty]$, so the inequality is meaningful when either side is infinite.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, first paragraph (last sentence)

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting
import Definitions.Def_StochasticOrders_Usual_UsualOrder

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603: if `X₁ ≤st X₂` and both are nonnegative, then `𝔼[X₁ⁿ] ≤ 𝔼[X₂ⁿ]`
for every real `n > 0`; in particular a finite `n`-th moment of `X₂` gives one of `X₁`. -/
theorem nthMoment_mono_of_usualOrder (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (h₁ : ν₁ (Set.Iio 0) = 0) (h₂ : ν₂ (Set.Iio 0) = 0)
    (hst : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id) (n : ℝ) (hn : 0 < n) :
    nthMoment ν₁ n ≤ nthMoment ν₂ n := by sorry

end LariviereIGFR.Moments
