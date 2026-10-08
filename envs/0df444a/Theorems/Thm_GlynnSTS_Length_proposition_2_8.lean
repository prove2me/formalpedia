-- Prove2me | Theorems.Thm_GlynnSTS_Length_proposition_2_8
-- name    : GlynnSTS.Length.proposition_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:48.701486+00:00
-- url     : https://prove2.me/theorems/8fdccbc6-78de-468e-b7b4-a7bcadfc4928
-- title:
--   Proposition 2.8 — Brownian endpoint and STS scale are independent
-- statement:
--   Let $B$ be standard Brownian motion on $[0,1]$ and let $g$ belong to the class $\mathcal M$ of admissible STS scale functionals. Then
--   $$
--   B(1)\ \text{is independent of}\ g(B).
--   $$
--   This independence lets the law of the standardized endpoint be written as a normal scale mixture.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 4, Proposition 2.8

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Proposition 2.8, p. 4: the Brownian endpoint and the STS scale are independent. -/
theorem proposition_2_8 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g) :
    IndepFun (fun ω => B ω 1) (fun ω => g (B ω)) P := by sorry

end GlynnSTS.Length
