-- Prove2me | Theorems.Thm_Milnor_isPolycyclic_of_isPolycyclic_quotient_of_not_hasExponentialGrowth
-- name    : Milnor.isPolycyclic_of_isPolycyclic_quotient_of_not_hasExponentialGrowth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T22:30:56.376142+00:00
-- url     : https://prove2.me/theorems/6ab0fa72-d398-4eef-b4b1-ebfed7c20cde
-- title:
--   Lemma 3: if $B/A$ is polycyclic and $B$ is not of exponential growth, then $B$ is polycyclic
-- statement:
--   Let $B$ be a finitely generated group and $A$ an abelian normal subgroup. If $B/A$ is
--   polycyclic and $B$ does not have exponential growth, then $B$ is polycyclic.
-- source:
--   Milnor, J., Growth of finitely generated solvable groups, Journal of Differential Geometry 2 (1968) 447–449, https://doi.org/10.4310/jdg/1214428659, Lemma 3, p. 448

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Milnor

/-- Milnor, Lemma 3 (p. 448), in the standing setting of a group extension `1 → A → B → C → 1`
with `A` abelian and `B` finitely generated: if `C` is polycyclic, and `B` does not have
exponential growth, then `B` must be polycyclic also. -/
theorem isPolycyclic_of_isPolycyclic_quotient_of_not_hasExponentialGrowth {B : Type*} [Group B]
    [Group.FG B] (A : Subgroup B) [A.Normal] [IsMulCommutative A]
    (hC : MilnorWolf.IsPolycyclic (B ⧸ A)) (h : ¬ Chou.HasExponentialGrowth B) :
    MilnorWolf.IsPolycyclic B := by
  sorry

end Milnor
