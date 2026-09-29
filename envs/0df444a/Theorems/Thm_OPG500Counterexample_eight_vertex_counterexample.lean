-- Prove2me | Theorems.Thm_OPG500Counterexample_eight_vertex_counterexample
-- name    : OPG500Counterexample.eight_vertex_counterexample
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T04:08:38.44451+00:00
-- url     : https://prove2.me/theorems/5c4997cd-9945-4028-b853-4ad91c324535
-- title:
--   An eight-vertex candidate counterexample to OPG-500
-- statement:
--   Let $H$ be the fixed graph on vertices $0,\ldots,7$ with edge set
--
--   $$
--   \{01,02,03,04,05,06,12,13,14,15,17,23,24,26,27,35,36,37\}.
--   $$
--
--   The target asserts that $H$ is 3-connected and that
--
--   $$
--   \forall \ell:E(H)\to\mathbb R,\quad
--   (\forall e,\ 0<\ell(e))\Longrightarrow
--   \exists C,\quad C\text{ is an $\ell$-geodesic simple cycle and is not peripheral}.
--   $$
--
--   The cycle may depend on the weighting, and tied shortest paths are included. This is an open formal target: the candidate repository and finite computations are not themselves a proof.
-- source:
--   Target source: Open Problem Garden OPG-500, https://www.openproblemgarden.org/op/geodesic_cycles_and_tuttes_theorem, with the proposed fixed obstruction in candidate C10: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md

import Definitions.Def_opg500_eight_vertex_graph

namespace OPG500Counterexample

/-- The fixed eight-vertex graph is 3-connected and, for every strictly positive
real edge weighting, has a vertex-geodesic simple cycle that is not peripheral. -/
theorem eight_vertex_counterexample :
    IsThreeConnected H ∧
      ∀ ℓ : EdgeWeight H, IsPositive ℓ →
        ∃ C : Cycle H, C.IsGeodesic ℓ ∧ ¬ C.IsPeripheral := by sorry

end OPG500Counterexample
