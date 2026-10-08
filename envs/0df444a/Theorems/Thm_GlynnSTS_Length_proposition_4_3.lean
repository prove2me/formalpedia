-- Prove2me | Theorems.Thm_GlynnSTS_Length_proposition_4_3
-- name    : GlynnSTS.Length.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:40.953645+00:00
-- url     : https://prove2.me/theorems/a37c3009-1d9b-48dc-93d1-24a3ee218438
-- title:
--   Proposition 4.3 — the centered STS interval has least width
-- statement:
--   Let $g\in\mathcal M$, $0<\delta<1$, and let $z$ solve $H(z)=1-\delta/2$. The symmetric endpoints $\alpha=-z$ and $\beta=z$ give confidence mass $1-\delta$, and every other pair with the same mass has at least their width:
--   $$
--   H(z)-H(-z)=1-\delta,\qquad
--   H(\beta)-H(\alpha)=1-\delta\ \Longrightarrow\ 2z\le\beta-\alpha.
--   $$
--   Thus centering minimizes the interval's quantile width.
--
--   **Formalization Note** The quantile $z$ is specified by its defining equation; no real infimum is taken.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 10, Proposition 4.3

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Proposition 4.3, p. 10: a centered STS interval minimizes the quantile width. -/
theorem proposition_4_3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (z : ℝ) (hz : H P B g z = 1 - δ / 2) :
    H P B g z - H P B g (-z) = 1 - δ ∧
      ∀ α β : ℝ, H P B g β - H P B g α = 1 - δ →
        2 * z ≤ β - α := by sorry

end GlynnSTS.Length
