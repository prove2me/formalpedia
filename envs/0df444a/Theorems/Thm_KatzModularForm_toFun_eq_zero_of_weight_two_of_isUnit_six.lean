-- Prove2me | Theorems.Thm_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six
-- name    : KatzModularForm.toFun_eq_zero_of_weight_two_of_isUnit_six
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/7f2f127b-798b-5eaa-8f5d-8ce6a4349b6e
-- title:
--   Weight-two level-one Katz forms vanish when 6 is invertible
-- statement:
--   Let $R$ be a commutative ring in which $6$ is a unit, and let $F$ be a Katz modular form of weight $2$ over $R$: a rule assigning to every $R$-algebra $A$ and every Weierstrass curve $W$ over $A$ with unit discriminant an element $F(W) \in A$, compatible with $R$-algebra maps (the value on the base change of $W$ along $f : A \to B$ is $f$ applied to the value on $W$) and satisfying $F(C \bullet W) = (C.u^{-1})^{2} \, F(W)$ for every variable change $C$ over $A$. Suppose the $q$-expansion of $F$, namely its value on the Tate curve over the Laurent series ring $\mathrm{LaurentSeries}\ R$ (the Tate Weierstrass curve over $\mathbb{Z}[[q]]$ base-changed along the canonical map into $\mathrm{LaurentSeries}\ R$), comes from a power series: there is $g \in R[[q]]$ with $F.\mathrm{qExpansion} = \mathrm{HahnSeries.ofPowerSeries}\ \mathbb{Z}\ R\ g$, i.e. the expansion has no terms of negative degree. Then for every $R$-algebra $A$ and every Weierstrass curve $W$ over $A$ whose discriminant $W.\Delta$ is a unit, $F(W) = 0$.
--
--   This is the statement that there are no nonzero weight-two modular forms of level one, in Katz's functorial formulation, once $6$ is invertible in the base and holomorphy at the cusp is imposed. It is used by [`KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two`](thm.html#KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two), which records the corresponding structure of weight-two forms over a general base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.lean

import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KatzModularForm.toFun_eq_zero_of_weight_two_of_isUnit_six
    (R : Type) [CommRing R] (h6 : IsUnit (6 : R)) (F : KatzModularForm R 2)
    (g : PowerSeries R) (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ R g)
    (A : Type) [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    F.toFun W hW = 0 := by sorry
