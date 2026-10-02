-- Prove2me | Theorems.Thm_MooreFoelner_isTree_treeAct_and_isPartialAction
-- name    : MooreFoelner.isTree_treeAct_and_isPartialAction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:11:06.001438+00:00
-- url     : https://prove2.me/theorems/1bb81af2-0440-424d-b538-733bd22cfb93
-- title:
--   §2 — the pointwise image of a tree is a tree, giving a partial right action of F
-- statement:
--   If $T$ is a tree and $T \cdot f$ is defined, then $T \cdot f$ is a tree; and $T \mapsto T \cdot f$ is a partial right action of Moore's $F$ (Definition 3.1).
--
--   **Formalization Note.** The action is defined on all finite sets of sequences, and the statement asserts the partial-action axioms there, including the composition law of the §3 definitions (see the note on Definition 3.1 there); on trees it is Moore's action on $\mathscr T$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isTree_treeAct_and_isPartialAction :
    (∀ (T T' : Finset Seq) (f : MooreF), IsTree T → treeAct T f = some T' → IsTree T') ∧
      IsPartialAction treeAct := by
  sorry

end MooreFoelner
