-- Prove2me | Theorems.Thm_MongeKantorovichYao_exists_cyclicallyMonotone_plan
-- name    : MongeKantorovichYao.exists_cyclicallyMonotone_plan
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T20:09:17.617974+00:00
-- url     : https://prove2.me/theorems/99f70c4d-c3b3-4394-af86-2f86264d2bb8
-- title:
--   Proposition 4.17 — existence of a cyclically monotone transference plan
-- statement:
--   Let $X,Y$ be Polish spaces with their Borel σ-algebras, $\mu$ and $\nu$ Borel probability measures on $X$ and $Y$, and $c : X\times Y\to[0,\infty)$ a continuous cost function. Then there exists a transference plan $\pi\in\Pi(\mu,\nu)$ which is $c$-cyclically monotone, i.e. concentrated on a $c$-cyclically monotone subset of $X\times Y$.
--
--   This extends Proposition 4.4 from empirical measures to arbitrary marginals and supplies the plan on which the dual potentials are built.
--
--   **Formalization Note** Nonnegativity of $c$ is the standing restriction of Section 4 ("continuous nonnegative cost functions").
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 11, Proposition 4.17 (proof pp. 11–12); standing assumptions of Section 4 (p. 6)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem exists_cyclicallyMonotone_plan {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p) :
    ∃ π ∈ transferencePlans μ ν, IsCCyclicallyMonotonePlan c π := by sorry

end MongeKantorovichYao
