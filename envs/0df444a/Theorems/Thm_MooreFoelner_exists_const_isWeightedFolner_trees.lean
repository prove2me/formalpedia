-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_isWeightedFolner_trees
-- name    : MooreFoelner.exists_const_isWeightedFolner_trees
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:41:22.919865+00:00
-- url     : https://prove2.me/theorems/5bfeefd3-96ef-4dc8-83c8-c08bfbb6f80d
-- title:
--   Lemma 4.2 — a Følner set of F gives a weighted Følner set of trees
-- statement:
--   There is a constant $C$ such that for every $\varepsilon$-Følner set $A \subseteq F$ (with respect to $\Gamma = \{x_0^{\pm1}, x_1^{\pm1}\}$) there is a weighted $C\varepsilon$-Følner set of trees $\mu$, for the action of $F$ on trees, whose support lies in $\{R_f : f \in A\}$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 11, Lemma 4.2

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem exists_const_isWeightedFolner_trees :
    ∃ C : ℝ, ∀ (ε : ℝ) (A : Finset MooreF), IsFolnerSet gens A ε →
      ∃ μ : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens μ (C * ε) ∧
        ↑μ.support ⊆ {T | ∃ f ∈ A, T = Rf (toMap f)} := by
  sorry

end MooreFoelner
