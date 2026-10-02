-- Prove2me | Theorems.Thm_MooreFoelner_treeAct_delta
-- name    : MooreFoelner.treeAct_delta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:54:22.810551+00:00
-- url     : https://prove2.me/theorems/193d16e6-4096-41a3-8a05-1c3d481ca03b
-- title:
--   Lemma 5.5 — ∂ commutes with elements acting properly on ∂T
-- statement:
--   If $T$ is a tree and $g$ in Moore's $F$ acts properly on $\partial T$, then $T \cdot g$ is defined and is a tree, $(\partial T) \cdot g$ is defined, and $\partial(T \cdot g) = (\partial T) \cdot g$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 14, Lemma 5.5

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem treeAct_delta (g : MooreF) (T : Finset Seq) (hT : IsTree T)
    (hg : ActsProperlyOn g (delta T)) :
    ∃ T', treeAct T g = some T' ∧ IsTree T' ∧ treeAct (delta T) g = some (delta T') := by
  sorry

end MooreFoelner
