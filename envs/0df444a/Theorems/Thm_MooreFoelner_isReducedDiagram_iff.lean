-- Prove2me | Theorems.Thm_MooreFoelner_isReducedDiagram_iff
-- name    : MooreFoelner.isReducedDiagram_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:27:30.391054+00:00
-- url     : https://prove2.me/theorems/733cb7a8-ebcd-4625-a343-708ec4ab7a3e
-- title:
--   §2 — a tree diagram is reduced iff it has no common caret
-- statement:
--   A tree diagram $(S, T)$ is reduced if and only if there is no $i$ with $i + 1 < |S|$ such that the $i$th elements of $S$ and $T$ (in lexicographic order) both end in $0$ and the $(i+1)$th elements both end in $1$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2 (citing Cannon–Floyd–Parry)

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isReducedDiagram_iff (S T : Finset Seq) (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔
      ¬ ∃ (i : ℕ) (hi : i + 1 < (sorted S).length) (hi' : i + 1 < (sorted T).length),
        ((sorted S).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted T).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted S).get ⟨i + 1, hi⟩).getLast? = some true ∧
        ((sorted T).get ⟨i + 1, hi'⟩).getLast? = some true := by
  sorry

end MooreFoelner
