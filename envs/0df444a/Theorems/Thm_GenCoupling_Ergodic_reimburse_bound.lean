-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_reimburse_bound
-- name    : GenCoupling.Ergodic.reimburse_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:39.227702+00:00
-- url     : https://prove2.me/theorems/247be5f6-8991-4197-bc9e-79e1d216736d
-- title:
--   Display in the proof of Theorem 2.3(i), p. 8 — W_d(Law X, ν) ≤ E d(X, Y) + d_TV(Law Y, ν) for 0 ≤ d ≤ 1
-- statement:
--   Let $E$ be a Polish space, $d:E\times E\to[0,1]$ measurable, $\gamma$ a probability measure on $E\times E$ (the joint law of a pair $(X,Y)$) and $\nu$ a Borel probability measure on $E$. Then
--   $$W_d(\mathrm{Law}(X),\nu)\le \mathsf E\, d(X,Y)+d_{TV}(\mathrm{Law}(Y),\nu),$$
--   where $\mathrm{Law}(X),\mathrm{Law}(Y)$ are the marginals of $\gamma$ and $\mathsf E\,d(X,Y)=\int d\,d\gamma$.
--
--   This is the first three lines of the chain of inequalities in the proof of Theorem 2.3(i) (and reused in part (iii)): the generalized coupling controls $\mathsf E d(X,Y)$, and the defect in law of $Y$ is paid back by the total variation term (the Control-and-Reimburse strategy of Remark 2.4).
--
--   **Formalization Note** The page applies this to $d=d_N$, $X=X^{x,y}_t$, $Y=Y^{x,y}_t$, $\nu=P_t(y,\cdot)$; the statement abstracts to any measurable $d$ with values in $[0,1]$.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, proof of Theorem 2.3(i), display, lines 1–3

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Display in the proof of Theorem 2.3(i), p. 8, lines 1–3: for a measurable `d` with
`0 ≤ d ≤ 1`, a probability measure `γ` on `E × E` (the joint law of `(X, Y)`) and a probability
measure `ν`, `W_d(Law X, ν) ≤ E d(X, Y) + d_TV(Law Y, ν)`. -/
theorem reimburse_bound {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (d : E → E → ℝ) (hd : Measurable (fun p : E × E => d p.1 p.2))
    (hd0 : ∀ x y, 0 ≤ d x y) (hd1 : ∀ x y, d x y ≤ 1)
    (γ : Measure (E × E)) [IsProbabilityMeasure γ] (ν : Measure E) [IsProbabilityMeasure ν] :
    W d (γ.map Prod.fst) ν
      ≤ ∫⁻ p, ENNReal.ofReal (d p.1 p.2) ∂γ
        + ENNReal.ofReal (MarkovChainCLT.tvDist (γ.map Prod.snd) ν) := by sorry

end GenCoupling.Ergodic
