-- Prove2me | Theorems.Thm_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow
-- name    : KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/8dbc45b8-0de6-592d-8a17-333657801d91
-- title:
--   Weight-two Katz forms mod 3^e are multiples of b₂
-- statement:
--   Fix a natural number $e$ and let $F$ be a Katz modular form of weight $2$ and level one over the ring $\mathbb{Z}/3^e$: that is, a rule $F$ assigning to every $\mathbb{Z}/3^e$-algebra $A$ and every Weierstrass curve $W$ over $A$ whose discriminant $W.\Delta$ is a unit an element $F(W) \in A$, compatible with $\mathbb{Z}/3^e$-algebra maps $f : A \to B$ in the sense that $F(f_*W) = f(F(W))$, and transforming under a variable change $C$ with unit scaling factor $C.u$ by $F(C \cdot W) = (C.u^{-1})^{2} \, F(W)$. Let $g$ be a power series over $\mathbb{Z}/3^e$ and assume that the $q$-expansion of $F$, namely the value of $F$ on the Tate curve over the Laurent series ring $\mathbb{Z}/3^e((q))$ (the base change of the integral Tate Weierstrass curve, whose discriminant is a unit), is the Laurent series attached to $g$; thus the $q$-expansion is assumed to have no terms of negative degree. The conclusion is that there exists $a \in \mathbb{Z}/3^e$ with $3a = 0$ such that for every $\mathbb{Z}/3^e$-algebra $A$ and every Weierstrass curve $W$ over $A$ with $W.\Delta$ a unit, $F(W) = \mathrm{alg}(a) \cdot W.b_2$, where $\mathrm{alg}$ is the structure map $\mathbb{Z}/3^e \to A$ and $b_2 = a_1^2 + 4a_2$.
--
--   This is the $3$-primary part of the classical determination of level-one Katz forms of weight two: modulo a power of $3$ the only such forms are the multiples $a\,b_2$ with $3a = 0$, so that $3b_2$ occurs modulo $9$ and nothing further. It is combined with the corresponding $2$-primary statement in [`KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two`](thm.html#KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two), and is used in [`ModularForm.three_dvd_qCoeff_zero_of_nine_dvd_qCoeff`](thm.html#ModularForm.three_dvd_qCoeff_zero_of_nine_dvd_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow.lean

import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_three_pow
    (e : ℕ) (F : KatzModularForm (ZMod (3^e)) 2) (g : PowerSeries (ZMod (3^e)))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod (3^e)) g) :
    ∃ a : ZMod (3^e), 3 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod (3^e)) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod (3^e)) A a * W.b₂ := by sorry
