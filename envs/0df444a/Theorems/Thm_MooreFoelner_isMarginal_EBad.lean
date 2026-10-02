-- Prove2me | Theorems.Thm_MooreFoelner_isMarginal_EBad
-- name    : MooreFoelner.isMarginal_EBad
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:02:12.940626+00:00
-- url     : https://prove2.me/theorems/b1f70051-dbd0-4494-bd47-536adad0b09a
-- title:
--   Lemma 5.7 — the trees satisfying neither (+) nor (−) form a marginal set
-- statement:
--   The set $\mathscr E$ of trees $T$ with neither $|T/001| < |T/01| < |T/10|$ nor $|T/001| > |T/01| > |T/10|$ is marginal for the action of Moore's $F$ on trees.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 14, Lemma 5.7

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isMarginal_EBad : IsMarginal treeAct EBad := by
  sorry

end MooreFoelner
