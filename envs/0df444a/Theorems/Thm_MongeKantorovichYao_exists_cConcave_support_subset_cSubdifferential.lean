-- Prove2me | Theorems.Thm_MongeKantorovichYao_exists_cConcave_support_subset_cSubdifferential
-- name    : MongeKantorovichYao.exists_cConcave_support_subset_cSubdifferential
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T20:15:57.055626+00:00
-- url     : https://prove2.me/theorems/8d447573-af0f-4d7b-8494-8bc7c4a3fdbe
-- title:
--   Proposition 4.22 — support of a cyclically monotone plan lies in a $c$-subdifferential
-- statement:
--   Let $X,Y$ be Polish spaces with their Borel σ-algebras and let $c : X\times Y\to[0,\infty)$ be continuous and bounded. Let $\pi$ be a Borel probability measure on $X\times Y$ that is $c$-cyclically monotone. Then there is a $c$-concave function $\psi : X\to\mathbb R$ such that
--   $$\operatorname{Support}(\pi)\subseteq\partial_c\psi=\{(x,y) : \psi^c(y)+\psi(x)=c(x,y)\}.$$
--
--   This produces the potential $\psi$ which, together with $\varphi=\psi^c$, attains equality in the duality.
--
--   **Formalization Note** The source states the conclusion with "c-convex" but constructs and uses a $c$-concave function in the sense of Definition 4.18; the $c$-concave form is formalized. The source takes $\psi$ real-valued; for a real-valued potential to exist in general, $c$ is assumed bounded here, which is the hypothesis under which the source uses this proposition (Proposition 4.31). Without boundedness a real-valued potential can fail to exist (e.g. quadratic cost on $\mathbb R$ with a plan supported on the graph of the derivative of a convex function finite only on $(-1,1)$). The support is the set of points all of whose neighbourhoods have positive measure, which in Polish spaces is the smallest closed set of full measure (Definition 4.21).
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 13, Proposition 4.22 (proof pp. 13–15), with Definitions 4.18–4.21; boundedness of $c$ as in Proposition 4.31 (p. 16)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem exists_cConcave_support_subset_cSubdifferential {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (c : X × Y → ℝ) (hc_cont : Continuous c) (hc_nonneg : ∀ p, 0 ≤ c p)
    (hc_bdd : BddAbove (Set.range c))
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (hπ : IsCCyclicallyMonotonePlan c π) :
    ∃ ψ : X → ℝ, IsCConcave c ψ ∧ π.support ⊆ cSubdifferential c ψ := by sorry

end MongeKantorovichYao
