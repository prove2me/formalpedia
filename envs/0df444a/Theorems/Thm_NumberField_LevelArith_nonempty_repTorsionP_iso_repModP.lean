-- Prove2me | Theorems.Thm_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP
-- name    : NumberField.LevelArith.nonempty_repTorsionP_iso_repModP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/9fc23c00-99a5-5365-bc3b-4aedc3833172
-- title:
--   A[p] ≅ A/pA as ℤ/p-representations when p ∤ |G|
-- statement:
--   Let $G$ be a finite group, let $p$ be a prime, and assume that the cardinality of $G$ is coprime to $p$. Let $A$ be an object of `Rep ℤ G`, i.e. an abelian group $A$ (carried in the bottom universe) with a $\mathbb{Z}$-linear $G$-action $\rho$, and assume the underlying set of $A$ is finite. Then the type of isomorphisms, in the category `Rep (ZMod p) G`, between `repTorsionP p A` and `repModP p A` is nonempty. Here `repTorsionP p A` is the object of `Rep (ZMod p) G` given by the submodule `Submodule.torsionBy ℤ A (p : ℤ)` of elements killed by $p$, with the $G$-action obtained by restricting $\rho$ (each $\rho(g)$ preserves this submodule) and with scalars reduced from $\mathbb{Z}$ to $\mathbb{Z}/p$; and `repModP p A` is the quotient $A/(p\cdot\top)$, i.e. $A/pA$, with the induced $G$-action and the same reduction of scalars. Thus $A[p]$ and $A/pA$ are isomorphic as $\mathbb{Z}/p$-linear representations of $G$.
--
--   This is the standard comparison of the $p$-torsion subgroup with the mod-$p$ reduction of a finite integral $G$-module in the case where the group order is prime to $p$, packaged on the level of the category of $\mathbb{Z}/p$-linear representations. It feeds the computations of invariants of `repModP` of the $S$-unit representation and the analysis of the mod-$p$ cyclotomic quotient in degree two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith Pointwise

theorem NumberField.LevelArith.nonempty_repTorsionP_iso_repModP
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hG : (Nat.card G).Coprime p)
    (A : Rep.{0} ℤ G) [Finite A] :
    Nonempty (repTorsionP p A ≅ repModP p A) := by sorry
