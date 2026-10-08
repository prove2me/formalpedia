-- Prove2me | Theorems.Thm_GlynnSTS_Length_proposition_2_7
-- name    : GlynnSTS.Length.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:49.861015+00:00
-- url     : https://prove2.me/theorems/8db8efc3-dd19-49c2-95c1-ee60cafdc178
-- title:
--   Proposition 2.7 — the two descriptions of the STS class agree
-- statement:
--   Let $\Gamma x(t)=x(t)-t x(1)$. For a standard Brownian motion $B$, let $\mathcal M$ be the class of measurable, positively homogeneous functionals invariant under linear shifts that are positive at $B$ almost surely and continuous there almost surely. Let $\mathcal N$ comprise measurable, positively homogeneous functionals $b$ for which $b(\Gamma B)>0$ almost surely and $b\circ\Gamma$ is continuous at $B$ almost surely. Then
--   $$
--   \mathcal M=\{b\circ\Gamma:b\in\mathcal N\}.
--   $$
--   This identifies the STS scale functionals as functions of the Brownian bridge.
--
--   **Formalization Note** Measurability of $b$ is explicit, as a standing convention for the paper's functionals.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 4, Proposition 2.7 and (2.6)

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Proposition 2.7, p. 4: the two descriptions of the STS class agree. -/
theorem proposition_2_7 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B) :
    ∀ g : C(unitInterval, ℝ) → ℝ,
      GlynnSTS.Limit.ClassM P B g ↔ ∃ b, ClassN P B b ∧ g = b ∘ Gamma := by sorry

end GlynnSTS.Length
