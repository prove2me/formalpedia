-- Prove2me | Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk
-- name    : ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/6899216d-5c35-5991-b9fc-7c42bd693d5f
-- title:
--   Equal classes in Pt differ by a variable change
-- statement:
--   Let $A$ be a commutative ring and let $R$ be a rigid Weierstrass datum over $A$, i.e. an element of [`ModularCurve.RigidWeierstrassData A`](def/ModularCurve_WeierstrassLevelModuliDatum.html#L11): a family of types $R.\mathrm{Raw}\,T$ indexed by the $A$-algebras $T$, together with a Weierstrass curve $R.\mathrm{curve}\,x$ over $T$ attached to each raw datum $x$ whose discriminant $\Delta$ is a unit, a functorial base-change operation $R.\mathrm{mapRing}$ along $A$-algebra maps (compatible with the identity, with composition, and carrying $R.\mathrm{curve}$ to the base change of the curve), and an action $R.\mathrm{act}$ of the group `WeierstrassCurve.VariableChange T` of admissible changes of variables over $T$ which is unital and multiplicative, transforms the associated curve by $R.\mathrm{curve}(R.\mathrm{act}\,C\,x) = C \bullet R.\mathrm{curve}\,x$, and commutes with base change. Let $T$ be an $A$-algebra and let $x, y \in R.\mathrm{Raw}\,T$ be raw data whose classes in the quotient $R.\mathrm{Pt}\,T$ of $R.\mathrm{Raw}\,T$ by the relation `R.Rel` coincide, that is $\mathrm{Quot.mk}\ x = \mathrm{Quot.mk}\ y$. Then there exists a change of variables $C :$ `WeierstrassCurve.VariableChange T` with $y = R.\mathrm{act}\,C\,x$; equivalently, `R.Rel` already relates $x$ and $y$, with no chains needed.
--
--   This is the statement that two raw Weierstrass-with-level data representing the same point of $R.\mathrm{Pt}\,T$ are related by a single admissible change of variables, i.e. that passing to the quotient loses no information beyond the variable-change action. It is the standard device for choosing representatives of points, and is used throughout the full-level chart and Tate-curve computations, for instance in the lemmas producing level automorphisms on algebraic charts and in the Diamond-operator origin-chart lemma.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk
    {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] (x y : R.Raw T)
    (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) :
    ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x := by sorry
