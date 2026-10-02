-- Prove2me | Theorems.Thm_MooreFoelner_exists_max_deltaConditions
-- name    : MooreFoelner.exists_max_deltaConditions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:46:18.46522+00:00
-- url     : https://prove2.me/theorems/ee97f4ad-e740-4246-a31a-68df536e09b8
-- title:
--   Lemma 5.2 — among trees satisfying the conditions for ∂T there is a greatest
-- statement:
--   Let $T$ be a tree. If some tree $U$ dominated by $T$ satisfies the defining conditions for $\partial T$, then there is such a $U$ that dominates every other such tree.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 11, Lemma 5.2

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem exists_max_deltaConditions (T : Finset Seq) (hT : IsTree T)
    (h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U) :
    ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U := by
  sorry

end MooreFoelner
