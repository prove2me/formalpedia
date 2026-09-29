-- Prove2me | Theorems.Thm_ModularCurve_map_slotSubst
-- name    : ModularCurve.map_slotSubst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/61d81271-49c9-5161-8913-27f05a6c3f35
-- title:
--   Slot substitution commutes with base change
-- statement:
--   Let $A$ and $B$ be commutative rings, $g : A \to B$ a ring homomorphism, $p$ and $j$ natural numbers with $0 < j$ and $j < p$, $c$ a unit of $A$, and $f$ a formal power series in two variables (indexed by `Fin 2`) over $\mathbb Z$. For a commutative ring $K$, a unit $c$ of $K$ and indices $p, j$, the project's `slotFamily K p c j` is the pair of one-variable power series $\big(C(c)\,X^{j},\ C(c^{-1})\,X^{p-j}\big)$ over $K$, and `slotSubst K p c j f` is the substitution `MvPowerSeries.subst` of this pair into $f$, a power series in one variable over $K$. The assertion is that applying the coefficientwise map induced by $g$ to `slotSubst A p c j f` yields `slotSubst B p (Units.map g c) j f`, where `Units.map g c` is the image of $c$ as a unit of $B$; that is, specialising $f$ at the slot $(c\,X^{j}, c^{-1}X^{p-j})$ over $A$ and then pushing forward along $g$ agrees with specialising $f$ at the corresponding slot over $B$.
--
--   This is the base-change compatibility of the slot specialisation attached to a Tate-type parametrisation: the $q$-expansion obtained by substituting $(c\,X^j, c^{-1}X^{p-j})$ into an integral two-variable series commutes with change of coefficient ring. It is used in the construction of level automorphisms with prescribed effect on slot expansions, in [`ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_mem_chartAlgFin_coe_eq_slotSubst_sub_and_apply_eq_laurent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_slotSubst.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.map_slotSubst
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (p : ℕ) (c : Aˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    (ModularCurve.slotSubst A p c j f).map g = ModularCurve.slotSubst B p (Units.map (g : A →* B) c) j f := by sorry
