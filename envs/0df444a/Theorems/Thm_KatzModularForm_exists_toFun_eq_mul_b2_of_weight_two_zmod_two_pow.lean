-- Prove2me | Theorems.Thm_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow
-- name    : KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2cd6fe72-8616-53b6-a1d2-1ed03f68a6db
-- title:
--   Weight-two Katz forms mod 2^e are 4-torsion multiples of b₂
-- statement:
--   Let $e$ be a natural number and let $F$ be a Katz modular form of weight $2$ and level one over $R=\mathbb{Z}/2^e$: that is, $F$ assigns to every $R$-algebra $A$ and every Weierstrass curve $W$ over $A$ with invertible discriminant $\Delta$ an element $F(W)\in A$, functorially in $R$-algebra maps, and such that for a variable change $C$ with unit scalar $u$ one has $F(C\cdot W)=u^{-2}F(W)$. Suppose $g$ is a power series over $\mathbb{Z}/2^e$ whose image under the embedding of power series into Hahn series (Laurent series) is the $q$-expansion of $F$, the latter being by definition the value of $F$ on the formal Tate curve over the Laurent series ring of $\mathbb{Z}/2^e$; thus $F$ is assumed holomorphic at the cusp with expansion $g$. The conclusion asserts the existence of $a\in\mathbb{Z}/2^e$ with $4a=0$ such that for every commutative ring $A$ in `Type` carrying a $\mathbb{Z}/2^e$-algebra structure and every Weierstrass curve $W$ over $A$ with $\Delta_W$ a unit, $F(W)$ equals the image of $a$ in $A$ times the invariant $b_2$ of $W$.
--
--   This is the $2$-primary half of Mazur's determination of the weight-two level-one forms: modulo $2^e$ the only such forms are the multiples $a\,b_2$ with $4a=0$, so that modulo $8$ nothing beyond $2b_2$ occurs. It feeds, together with the odd-primary computation, into [`KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two`](thm.html#KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two); the argument reduces along $\mathbb{Z}/2^e \to \mathbb{Z}/2$ and uses the obstruction modulo $8$ recorded in [`KatzModularForm.constantCoeff_ne_one_of_weight_two_zmod_eight`](thm.html#KatzModularForm.constantCoeff_ne_one_of_weight_two_zmod_eight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow.lean

import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KatzModularForm.exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow
    (e : ℕ) (F : KatzModularForm (ZMod (2^e)) 2) (g : PowerSeries (ZMod (2^e)))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod (2^e)) g) :
    ∃ a : ZMod (2^e), 4 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod (2^e)) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod (2^e)) A a * W.b₂ := by sorry
