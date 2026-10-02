-- Prove2me | Theorems.Thm_MooreFoelner_isMarginal_not_actsProperlyOn_delta
-- name    : MooreFoelner.isMarginal_not_actsProperlyOn_delta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:13:21.62+00:00
-- url     : https://prove2.me/theorems/251fb2b6-79dc-4dc4-869f-07254a67286b
-- title:
--   Lemma 5.12 — the trees on whose ∂ some generator does not act properly form a marginal set
-- statement:
--   The set of trees $T$ such that some element of $\Gamma$ does not act properly on $\partial T$ is marginal for the action of Moore's $F$ on trees.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 17, Lemma 5.12

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isMarginal_not_actsProperlyOn_delta :
    IsMarginal treeAct {T | IsTree T ∧ ¬ ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  sorry

end MooreFoelner
