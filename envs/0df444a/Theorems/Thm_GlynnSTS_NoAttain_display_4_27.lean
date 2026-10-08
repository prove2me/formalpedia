-- Prove2me | Theorems.Thm_GlynnSTS_NoAttain_display_4_27
-- name    : GlynnSTS.NoAttain.display_4_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:47.858986+00:00
-- url     : https://prove2.me/theorems/3f08beaf-fce5-42e0-8161-49b9d6445da2
-- title:
--   (4.27), p. 13 — P{ρ(σB, x) < ε} > 0 for every x ∈ C₀[0,1] and ε > 0
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$, regarded as a random element of $C[0,1]$, let $\sigma>0$, and let $\rho$ be the uniform metric on $C[0,1]$. For every $x\in C_0[0,1]=\{x\in C[0,1]: x(0)=0\}$ and every $\varepsilon>0$,
--   $$P\{\rho(\sigma B,x)<\varepsilon\}>0.$$
--
--   In words, every continuous path starting at $0$ lies in the topological support of the law of $\sigma B$ on $C[0,1]$. This is the first step of the proof of Proposition 4.26.
--
--   **Formalization Note** $\rho$ is the distance of the sup norm on `C(unitInterval, ℝ)`.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 13, (4.27) (proof of Proposition 4.26)

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

namespace GlynnSTS.NoAttain

open MeasureTheory ProbabilityTheory

/-- Display (4.27), p. 13: for every `σ > 0`, every `x ∈ C₀[0,1]` and every `ε > 0`,
`P{ρ(σB, x) < ε} > 0`, where `ρ` is the uniform metric on `C[0,1]`. -/
theorem display_4_27 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ x ∈ C0, ∀ ε : ℝ, 0 < ε → 0 < P {ω | dist (σ • B ω) x < ε} := by sorry

end GlynnSTS.NoAttain
