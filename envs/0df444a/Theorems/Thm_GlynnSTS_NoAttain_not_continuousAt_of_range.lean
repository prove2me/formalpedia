-- Prove2me | Theorems.Thm_GlynnSTS_NoAttain_not_continuousAt_of_range
-- name    : GlynnSTS.NoAttain.not_continuousAt_of_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:07.862645+00:00
-- url     : https://prove2.me/theorems/be161d62-633e-4919-9f1a-1cf0b29aadc7
-- title:
--   Proof of Proposition 4.26, p. 14 — if g takes every value ασ (σ > 0) in every ε-ball around x, then x ∈ D(g)
-- statement:
--   Let $g: C[0,1]\to\mathbb R$, $x\in C[0,1]$ and $\alpha>0$, and let $\rho$ be the uniform metric. Suppose that the range of $g$ over every $\varepsilon$-neighbourhood of $x$ contains the set $\{\alpha\sigma:\sigma>0\}$, that is, for every $\varepsilon>0$ and every $\sigma>0$ there is $y\in C[0,1]$ with
--   $$\rho(y,x)<\varepsilon\quad\text{and}\quad g(y)=\alpha\sigma .$$
--   Then $g$ is not continuous at $x$, i.e. $x\in D(g)$.
--
--   This is the deterministic step of the proof of Proposition 4.26 that converts the probabilistic information into a discontinuity of $g$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 14, proof of Proposition 4.26

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

namespace GlynnSTS.NoAttain

/-- The range claim of the proof of Proposition 4.26, p. 14: if, for some `α > 0`, the range
of `g` over every `ε`-neighbourhood of `x` contains the set `{ασ : σ > 0}`, then `g` is not
continuous at `x`, i.e. `x ∈ D(g)`. -/
theorem not_continuousAt_of_range (g : C(unitInterval, ℝ) → ℝ) (x : C(unitInterval, ℝ))
    (α : ℝ) (hα : 0 < α)
    (hrange : ∀ ε : ℝ, 0 < ε → ∀ σ : ℝ, 0 < σ → ∃ y, dist y x < ε ∧ g y = α * σ) :
    x ∈ GlynnSTS.Limit.D g := by sorry

end GlynnSTS.NoAttain
