-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
-- name    : NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/dd867fb2-5b15-5b2c-84a1-1799ef09e8f2
-- title:
--   Idele norm one for integral ideles with trivial archimedean part
-- statement:
--   Let $F$ be a number field and let $u$ be a unit of the adele ring $\mathbb{A}_F$ of $F$, the latter being realised as the product of the infinite adele ring $\prod_{w\mid\infty}F_w$ and the finite adele ring of the ring of integers $\mathcal{O}_F$. Assume two hypotheses. First, the archimedean component of $u$, that is the first coordinate of the underlying adele, is $1$. Second, the image of $u$ under `finitePartUnits`, the map of unit groups induced by the projection of $\mathbb{A}_F$ onto the finite adele ring, lies in the subgroup `unitIdeles`: for every $v$ in the height-one spectrum of $\mathcal{O}_F$ the $v$-component of that finite unit lies in the valuation ring $\mathcal{O}_{F_v}$ of the $v$-adic completion, and the same holds for every $v$-component of its inverse in the unit group of the finite adele ring. The conclusion is that `ideleNorm F u`, defined as the real number underlying the value at $u$ of the distributive Haar character of $\mathbb{A}_F$ (the factor by which multiplication by $u$ scales a Haar measure on $\mathbb{A}_F$), equals $1$.
--
--   This records the classical fact that an idele which is trivial at the archimedean places and a local unit at every finite place has module $1$, so lies in the norm-one subgroup of the idele group. It is used throughout the global Tate-theoretic and automorphic estimates built on the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdeleRing

theorem NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
    (F : Type) [Field F] [NumberField F] (u : (AdeleRing (𝓞 F) F)ˣ)
    (harch : (u : AdeleRing (𝓞 F) F).1 = 1)
    (hfin : finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F) :
    ideleNorm F u = 1 := by sorry
