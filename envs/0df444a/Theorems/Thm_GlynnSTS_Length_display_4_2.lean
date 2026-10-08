-- Prove2me | Theorems.Thm_GlynnSTS_Length_display_4_2
-- name    : GlynnSTS.Length.display_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:59.684981+00:00
-- url     : https://prove2.me/theorems/db8c2d5f-0c99-41b7-b703-6269c5485887
-- title:
--   Equation (4.2) — weak limit of the STS scale functional
-- statement:
--   Let the centered integrated simulation process obey Assumption (2.1), $X_n\Rightarrow\sigma B$ in $C[0,1]$, and let $g\in\mathcal M$. Then, as $n\to\infty$,
--   $$
--   g(X_n)\Rightarrow\sigma g(B).
--   $$
--   This is the distributional limit used for the expected-width asymptotics.
--
--   **Formalization Note** Joint measurability and pathwise integrability of the output process are included in the formal version of Assumption (2.1).
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 9, (4.2), proof of Proposition 4.1

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Equation (4.2), p. 9: the scale functional obeys the continuous mapping limit. -/
theorem display_4_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : Assumption21 P Y Ybar μ σ B) :
    TendstoInDistribution (fun (n : ℕ) ω => g (GlynnSTS.Limit.Xn Ybar μ n ω)) atTop
      (fun ω => σ * g (B ω)) (fun _ => P) P := by sorry

end GlynnSTS.Length
