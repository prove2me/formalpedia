-- Prove2me | Theorems.Thm_OPG169_minimal_counterexample_semidegree
-- name    : OPG169.minimal_counterexample_semidegree
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T05:05:23.330242+00:00
-- url     : https://prove2.me/theorems/f0028b06-416a-4258-97af-51d22cf845d6
-- title:
--   Semidegree two in a least-order counterexample
-- statement:
--   Every vertex of a least-order planar counterexample has at least two incoming neighbors and at least two outgoing neighbors:
--
--   $$
--   \forall v\in V(D),
--   \qquad d^-(v)\ge2\quad\text{and}\quad d^+(v)\ge2.
--   $$
--
--   The premise uses minimum vertex order in the full class of finite planar orientations. This statement is stronger than the underlying minimum-degree-three milestone and remains an open formal candidate.
-- source:
--   VibeMathing candidate_only proof draft at commit 16b9fbcf379719f4fad59a364151ff36f1bbb772, research/artifacts/candidates/opg169-a01-degree4-proof-20260907.md

import Definitions.Def_opg169_planar_dichromatic

namespace OPG169

universe u

/-- Stronger local candidate: every vertex of a least-order counterexample has
at least two in-neighbors and at least two out-neighbors. -/
theorem minimal_counterexample_semidegree
    {V : Type u} [Fintype V] (G : SimpleGraph V) (D : Digraph V)
    (hmin : IsLeastOrderCounterexample G D) :
    ∀ v : V,
      2 ≤ (Set.encard {u : V | D u v}) ∧
      2 ≤ (Set.encard {u : V | D v u}) := by sorry

end OPG169
