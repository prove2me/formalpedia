-- Prove2me | Theorems.Thm_MongeKantorovichYao_discrete_exists_cyclicallyMonotone_plan
-- name    : MongeKantorovichYao.discrete_exists_cyclicallyMonotone_plan
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T19:05:16.568224+00:00
-- url     : https://prove2.me/theorems/b0837722-cc97-4255-b9a8-77247508333a
-- title:
--   Proposition 4.4 — cyclically monotone plan between empirical measures
-- statement:
--   Let $X,Y$ be Polish spaces with their Borel σ-algebras, $c : X\times Y\to\mathbb R$ a cost function, $n\ge 1$, and $x_1,\dots,x_n\in X$, $y_1,\dots,y_n\in Y$ (not necessarily distinct). Put
--   $$\mu=\frac1n\sum_{i=1}^n\delta_{x_i},\qquad \nu=\frac1n\sum_{i=1}^n\delta_{y_i}.$$
--   Then there exists a $c$-cyclically monotone transference plan $\pi\in\Pi(\mu,\nu)$, i.e. a coupling of $\mu$ and $\nu$ concentrated on a $c$-cyclically monotone set.
--
--   This discrete case is the first step of the proof of Monge–Kantorovich duality: it is later extended to general marginals by approximation with empirical measures.
--
--   **Formalization Note** The finiteness of $c(x_i,y_j)$ required in the source is automatic since $c$ is real-valued. The Polish/Borel setting is the standing assumption of Section 4.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 7, Proposition 4.4 (proof pp. 7–9)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem discrete_exists_cyclicallyMonotone_plan {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (hn : 0 < n) (x : Fin n → X) (y : Fin n → Y) (c : X × Y → ℝ) :
    ∃ π ∈ transferencePlans ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (x i))
        ((n : ENNReal)⁻¹ • ∑ i, Measure.dirac (y i)),
      IsCCyclicallyMonotonePlan c π := by sorry

end MongeKantorovichYao
