-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_isFolnerSet_of_isFolnerSet
-- name    : MooreFoelner.exists_const_isFolnerSet_of_isFolnerSet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:52:08.912955+00:00
-- url     : https://prove2.me/theorems/c1154dc8-d0e4-4cee-b164-4b95b4b2862a
-- title:
--   §2 — changing the finite generating set changes Følner constants by a bounded factor
-- statement:
--   For every finite generating set $\Gamma'$ of Moore's $F$ there is $K > 0$ such that every set that is $\varepsilon$-Følner with respect to $\Gamma'$ is $K\varepsilon$-Følner with respect to $\Gamma = \{x_0, x_1, x_0^{-1}, x_1^{-1}\}$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem exists_const_isFolnerSet_of_isFolnerSet (Γ' : Finset MooreF)
    (hgen : Subgroup.closure (Γ' : Set MooreF) = ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : Finset MooreF) (ε : ℝ), IsFolnerSet Γ' A ε → IsFolnerSet gens A (K * ε) := by
  sorry

end MooreFoelner
