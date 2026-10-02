-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_isWeightedFolner_delta
-- name    : MooreFoelner.exists_const_isWeightedFolner_delta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:18:50.491982+00:00
-- url     : https://prove2.me/theorems/3ac465d1-e50e-443e-af70-e7a572b2a1ca
-- title:
--   Lemma 5.13 — ∂ carries weighted Følner sets of trees to weighted Følner sets of trees
-- statement:
--   There is a constant $C$ such that for every weighted $\varepsilon$-Følner set of trees $\mu$ (supported on trees) with $C\varepsilon \le 1$ there is a weighted $C\varepsilon$-Følner set of trees supported on $\{\partial T : \mu(T) > 0,\ \partial T \text{ non-trivial},\ \Gamma \text{ acts properly on } \partial T\}$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 18, Lemma 5.13

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem exists_const_isWeightedFolner_delta :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : Finset Seq →₀ ℝ), (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → C * ε ≤ 1 →
      ∃ ν : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens ν (C * ε) ∧
        ↑ν.support ⊆ {U | ∃ T, 0 < μ T ∧ U = delta T ∧ delta T ≠ trivialTree ∧
          ∀ γ ∈ gens, ActsProperlyOn γ (delta T)} := by
  sorry

end MooreFoelner
