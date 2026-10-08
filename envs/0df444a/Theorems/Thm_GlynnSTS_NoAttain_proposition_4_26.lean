-- Prove2me | Theorems.Thm_GlynnSTS_NoAttain_proposition_4_26
-- name    : GlynnSTS.NoAttain.proposition_4_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:39.749487+00:00
-- url     : https://prove2.me/theorems/ad19e682-9d0a-4d8e-84c8-02c28f46db4a
-- title:
--   Proposition 4.26, p. 13 — there is no g ∈ 𝓜 with P{g(σB) = ασ} = 1 for some α > 0
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$, regarded as a random element of $C[0,1]$, let $\sigma>0$, and let $\mathcal M$ be the class (2.3) of measurable, positively homogeneous, $k$-shift-invariant functions $g: C[0,1]\to\mathbb R$ with $P\{g(B)>0\}=1$ and $P\{B\in D(g)\}=0$. Then there is no $g\in\mathcal M$ such that
--   $$P\{g(\sigma B)=\alpha\sigma\}=1 \qquad (4.25)$$
--   holds for some $\alpha>0$.
--
--   By the proof of Theorem 4.8, the asymptotic lower bound $\liminf_{n\to\infty}n^{1/2}EL_n\ge2\sigma\Phi^{-1}(1-\delta/2)$ on the expected length of a standardized-time-series confidence interval (Corollary 4.16) could be attained by some $g\in\mathcal M$ only if (4.25) held. Proposition 4.26 therefore shows that the bound, although tight as an infimum over $\mathcal M$ by (4.23), is attained by no single $g\in\mathcal M$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 13, Proposition 4.26 and (4.25)

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

namespace GlynnSTS.NoAttain

open MeasureTheory ProbabilityTheory

/-- Proposition 4.26, p. 13: for a standard Brownian motion `B` and `σ > 0`, there is no
`g ∈ 𝓜` such that (4.25) `P{g(σB) = ασ} = 1` holds for some `α > 0`. -/
theorem proposition_4_26 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (σ : ℝ) (hσ : 0 < σ) :
    ¬ ∃ g : C(unitInterval, ℝ) → ℝ, GlynnSTS.Limit.ClassM P B g ∧
      ∃ α : ℝ, 0 < α ∧ ∀ᵐ ω ∂P, g (σ • B ω) = α * σ := by sorry

end GlynnSTS.NoAttain
