-- Prove2me | Theorems.Thm_GlynnSTS_NoAttain_small_ball_positive
-- name    : GlynnSTS.NoAttain.small_ball_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:12.264985+00:00
-- url     : https://prove2.me/theorems/1f083f03-21a2-4aef-a810-e03efcef68be
-- title:
--   Proof of Proposition 4.26, p. 14 — P{|B(t) − z| < η, max_{0≤s≤t}|B(s)| < 2η} > 0 for |z| < η
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$, regarded as a random element of $C[0,1]$. For every $t\in[0,1]$ and all real $\eta, z$ with $|z|<\eta$,
--   $$P\Big\{|B(t)-z|<\eta,\ \max_{0\le s\le t}|B(s)|<2\eta\Big\}>0.$$
--
--   This is the elementary positivity fact invoked in the proof of Proposition 4.26: a Brownian path can end near any point $z$ of $(-\eta,\eta)$ at time $t$ while staying inside the strip of half-width $2\eta$ up to time $t$. Applied on each subinterval $[k/N,(k+1)/N]$ together with independent increments, it yields that every path in $C_0[0,1]$ is charged by the law of $\sigma B$ (display (4.27)).
--
--   **Formalization Note** The paper applies the fact at $t=1/N>0$. The statement here also covers $t=0$, where it holds trivially because $B(0)=0$ almost surely; this makes it slightly stronger, not weaker. The maximum over $[0,t]$ is written as "for every $s\le t$", which is equivalent because the paths are continuous. The condition $|z|<\eta$ already forces $\eta>0$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 14, proof of Proposition 4.26 (after (4.29))

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

namespace GlynnSTS.NoAttain

open MeasureTheory ProbabilityTheory

/-- The small-ball fact used in the proof of Proposition 4.26 (p. 14): for a standard Brownian
motion `B`, every `t ∈ [0,1]`, and every `z` with `|z| < η`,
`P{|B(t) − z| < η, max_{0 ≤ s ≤ t} |B(s)| < 2η} > 0`. -/
theorem small_ball_positive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B) :
    ∀ t : unitInterval, ∀ η z : ℝ, |z| < η →
      0 < P {ω | |B ω t - z| < η ∧ ∀ s : unitInterval, s ≤ t → |B ω s| < 2 * η} := by sorry

end GlynnSTS.NoAttain
