-- Prove2me | Theorems.Thm_OPG500Counterexample_finite_geodesic_cycles_generate
-- name    : OPG500Counterexample.finite_geodesic_cycles_generate
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:07:34.444495+00:00
-- url     : https://prove2.me/theorems/0385a44b-4a8e-417b-ada5-ad91a861e223
-- title:
--   Theorem 3.1: weighted geodesic cycles generate the finite cycle space
-- statement:
--   Let $G$ be a finite simple graph and let $\ell:E(G)\to\mathbb R$ be strictly positive on every edge. For every simple cycle $C$ of $G$, there is a finite list of vertex-geodesic simple cycles such that each listed cycle $D$ satisfies
--
--   $$
--   \operatorname{length}_{\ell}(D)\leq\operatorname{length}_{\ell}(C),
--   $$
--
--   and the sum over $\mathbb F_2$ of their edge-indicator vectors is the edge-indicator vector of $C$. The statement permits repeated entries and does not assume unique shortest paths.
-- source:
--   Georgakopoulos--Sprüssel, Geodetic topological cycles in locally finite graphs, EJC 16 (2009), R144, https://arxiv.org/abs/0911.3999v1, Section 3.1, Theorem 3.1

import Definitions.Def_opg500_weighted_cycle_models

namespace OPG500Counterexample

universe u

/-- Georgakopoulos--Sprüssel, Theorem 3.1, in the finite vertex-geodesic form:
every cycle is a binary sum of no-longer geodesic cycles. -/
theorem finite_geodesic_cycles_generate
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : EdgeWeight G) (hpositive : IsPositive ℓ)
    (C : Cycle G) :
    ∃ cycles : List (Cycle G),
      (∀ D, D ∈ cycles →
        D.IsGeodesic ℓ ∧
          Walk.weightedLength ℓ D.walk ≤ Walk.weightedLength ℓ C.walk) ∧
      CycleList.edgeVectorSum cycles = C.edgeVector := by sorry

end OPG500Counterexample
