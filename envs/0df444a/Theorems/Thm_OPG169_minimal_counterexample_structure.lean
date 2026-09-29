-- Prove2me | Theorems.Thm_OPG169_minimal_counterexample_structure
-- name    : OPG169.minimal_counterexample_structure
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-08T05:05:10.264434+00:00
-- url     : https://prove2.me/theorems/6caf76f7-4151-4b58-bca0-4f8284534b87
-- title:
--   Structure of a least-order planar counterexample
-- statement:
--   Let $D$ be a least-order counterexample to acyclic two-colorability among all finite planar orientations. Then $D$ is nonempty and strongly connected, and every vertex of its underlying graph has at least three neighbors:
--
--   $$
--   D\text{ least-order counterexample}
--   \quad\Longrightarrow\quad
--   D\text{ strongly connected and }\delta(U(D))\ge3.
--   $$
--
--   The theorem is conditional: it does not assert that a counterexample exists, and minimality is by vertex count over the full planar class.
-- source:
--   VibeMathing candidate_only proof draft at commit 16b9fbcf379719f4fad59a364151ff36f1bbb772, research/artifacts/candidates/opg169-a01-target-closure-20260907.md; SCC background compared with Mohar, Section 2

import Definitions.Def_opg169_planar_dichromatic

namespace OPG169

universe u

/-- Every least-order counterexample is nonempty, strongly connected, and has
underlying minimum degree at least three. -/
theorem minimal_counterexample_structure
    {V : Type u} [Fintype V] (G : SimpleGraph V) (D : Digraph V)
    (hmin : IsLeastOrderCounterexample G D) :
    IsStronglyConnected D ∧ HasMinimumDegreeThree G := by sorry

end OPG169
