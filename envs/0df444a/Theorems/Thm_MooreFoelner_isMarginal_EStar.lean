-- Prove2me | Theorems.Thm_MooreFoelner_isMarginal_EStar
-- name    : MooreFoelner.isMarginal_EStar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:10:20.039003+00:00
-- url     : https://prove2.me/theorems/ce742bdb-51b2-445d-bb1f-feea855d5f14
-- title:
--   Lemma 5.10 — the trees satisfying neither (2×) nor (½×) form a marginal set
-- statement:
--   The set $\mathscr E^*$ of trees satisfying neither $(2\times)$ nor $(\tfrac12\times)$ is marginal for the action of Moore's $F$ on trees.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 16, Lemma 5.10

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isMarginal_EStar : IsMarginal treeAct EStar := by
  sorry

end MooreFoelner
