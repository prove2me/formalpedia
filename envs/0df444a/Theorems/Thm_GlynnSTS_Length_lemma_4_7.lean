-- Prove2me | Theorems.Thm_GlynnSTS_Length_lemma_4_7
-- name    : GlynnSTS.Length.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:10.873973+00:00
-- url     : https://prove2.me/theorems/85f91e5c-78c2-405a-8add-07e122b9881d
-- title:
--   Lemma 4.7 — scale invariance of the expected-width criterion
-- statement:
--   Let $g\in\mathcal M$, $0<\delta<1$, and $b>0$. Write $z_g$ and $z_{bg}$ for the solutions to $H_g(z_g)=H_{bg}(z_{bg})=1-\delta/2$. With expectations allowed to be infinite, the criterion $\psi(g)=E[g(B)]z_g$ obeys
--   $$
--   \psi(bg)=\psi(g),\quad\text{that is,}\quad
--   E[bg(B)]z_{bg}=E[g(B)]z_g.
--   $$
--   This scale invariance is used in the paper's lower bound for $\psi$.
--
--   **Formalization Note** Expectations are extended nonnegative integrals. Both quantiles are pinned by their defining equations.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 10, Lemma 4.7 and (4.6)

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Lemma 4.7, p. 10: the expected-scale/quantile product is invariant under rescaling. -/
theorem lemma_4_7 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (b : ℝ) (hb : 0 < b) (z z' : ℝ)
    (hz : H P B g z = 1 - δ / 2)
    (hz' : H P B (fun x => b * g x) z' = 1 - δ / 2) :
    (∫⁻ ω, ENNReal.ofReal (b * g (B ω)) ∂P) * ENNReal.ofReal z' =
      (∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P) * ENNReal.ofReal z := by sorry

end GlynnSTS.Length
