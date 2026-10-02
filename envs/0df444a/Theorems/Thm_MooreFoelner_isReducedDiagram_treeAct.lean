-- Prove2me | Theorems.Thm_MooreFoelner_isReducedDiagram_treeAct
-- name    : MooreFoelner.isReducedDiagram_treeAct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:46:34.798189+00:00
-- url     : https://prove2.me/theorems/65ac26e4-d25f-481a-af26-4efee2be9e46
-- title:
--   §2 — acting properly on the range tree of a reduced diagram keeps it reduced
-- statement:
--   If $(S, T)$ is a reduced tree diagram describing $g$, $f$ acts properly on $T$ and $T \cdot f = T'$, then $(S, T')$ is a reduced tree diagram describing $f \circ g$, which in Moore's $F$ is the product $g \cdot f$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isReducedDiagram_treeAct (f g : MooreF) (S T T' : Finset Seq)
    (h : IsReducedDiagram S T) (hg : Describes S T (toMap g)) (hf : ActsProperlyOn f T)
    (hT' : treeAct T f = some T') :
    IsReducedDiagram S T' ∧ Describes S T' (toMap (g * f)) := by
  sorry

end MooreFoelner
