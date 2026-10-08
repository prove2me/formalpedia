-- Prove2me | Theorems.Thm_GlynnSTS_Length_proposition_4_1_a
-- name    : GlynnSTS.Length.proposition_4_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:50.039545+00:00
-- url     : https://prove2.me/theorems/3b73b416-f4af-460f-a4ef-d724d92acc7e
-- title:
--   Proposition 4.1(a) — lower bound for scaled expected width
-- statement:
--   Let $g\in\mathcal M$ be nonnegative on all of $C[0,1]$. Assume $X_n\Rightarrow\sigma B$ with $\sigma>0$. Choose $0<\delta<1$ and endpoints $\alpha,\beta$ satisfying $H(\beta)-H(\alpha)=1-\delta$. For $L_n=g(\overline Y_n)(\beta-\alpha)$,
--   $$
--   \liminf_{n\to\infty}\sqrt n\,E[L_n]\ge
--   \sigma E[g(B)](\beta-\alpha).
--   $$
--   The proposition transfers the Brownian expected scale into a lower bound for the original simulation intervals.
--
--   **Formalization Note** Expectations and the liminf are in the extended nonnegative reals; no integrability of $g(B)$ is presumed. The confidence-mass condition pins the endpoints.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 9, Proposition 4.1(a)

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Proposition 4.1(a), p. 9: a lower bound for the scaled expected interval width. -/
theorem proposition_4_1_a {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (hg0 : ∀ x, 0 ≤ g x)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : Assumption21 P Y Ybar μ σ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (α β : ℝ) (hαβ : H P B g β - H P B g α = 1 - δ) :
    ENNReal.ofReal (σ * (β - α)) *
      (∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P) ≤
        liminf (fun n : ℕ => ENNReal.ofReal (Real.sqrt n) *
          ∫⁻ ω, ENNReal.ofReal (Ln g Ybar α β n ω) ∂P) atTop := by sorry

end GlynnSTS.Length
