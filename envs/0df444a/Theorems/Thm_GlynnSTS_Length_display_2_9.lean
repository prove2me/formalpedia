-- Prove2me | Theorems.Thm_GlynnSTS_Length_display_2_9
-- name    : GlynnSTS.Length.display_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:57.24719+00:00
-- url     : https://prove2.me/theorems/630b0abb-7406-4b67-ace7-1e352850d26e
-- title:
--   Equation (2.9) — normal scale mixture for the standardized endpoint
-- statement:
--   Let $B$ be standard Brownian motion, $g\in\mathcal M$, $G$ the law of $g(B)$, and $\Phi$ the standard normal distribution function. For $H(x)=P\{B(1)/g(B)\le x\}$, every real $x$ satisfies
--   $$
--   H(x)=\int_{(0,\infty)}\Phi(xy)\,G(dy).
--   $$
--   The law $G$ is concentrated on positive values. This formula is the distributional input for the interval quantiles and the expected-length bound.
--
--   **Formalization Note** $G$ is the measurable pushforward of the probability measure by $g\circ B$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 4, (2.9)

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Equation (2.9), p. 4: the law of the standardized endpoint is a normal scale mixture. -/
theorem display_2_9 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g) :
    ∀ x : ℝ, H P B g x =
      ∫ y in Set.Ioi (0 : ℝ), cdf (gaussianReal 0 1) (x * y)
        ∂(P.map (fun ω => g (B ω))) := by sorry

end GlynnSTS.Length
