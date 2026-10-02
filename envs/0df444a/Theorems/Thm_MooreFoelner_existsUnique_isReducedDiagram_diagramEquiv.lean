-- Prove2me | Theorems.Thm_MooreFoelner_existsUnique_isReducedDiagram_diagramEquiv
-- name    : MooreFoelner.existsUnique_isReducedDiagram_diagramEquiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:17:59.749367+00:00
-- url     : https://prove2.me/theorems/6bb0550a-543f-4ec5-a98f-9ad93aed015c
-- title:
--   §2 — every tree diagram is equivalent to a unique reduced tree diagram
-- statement:
--   Every tree diagram $(L, R)$ is equivalent to exactly one reduced tree diagram: there is exactly one pair $(L', R')$ that is a reduced tree diagram and defines the same map as $(L, R)$ on infinite sequences.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2 (citing Cannon–Floyd–Parry)

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem existsUnique_isReducedDiagram_diagramEquiv (L R : Finset Seq) (h : IsTreeDiagram L R) :
    ∃! D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 ∧ DiagramEquiv L R D.1 D.2 := by
  sorry

end MooreFoelner
