-- Prove2me | Theorems.Thm_KatzModularForm_exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
-- name    : KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/6dfff0b0-8769-59b6-b838-b1cdd5b63ab6
-- title:
--   Weight-two Katz forms mod M are 12-torsion multiples of b₂
-- statement:
--   Let $M$ be a natural number, and work over the ring $\mathbb{Z}/M$ (so $M=0$ gives $\mathbb{Z}$). Let $F$ be a Katz modular form of weight $2$ and level one over $\mathbb{Z}/M$: that is, a rule assigning to every $\mathbb{Z}/M$-algebra $A$ and every Weierstrass curve $W$ over $A$ with unit discriminant an element $F(W)\in A$, compatible with $\mathbb{Z}/M$-algebra maps $A\to B$ under base change of $W$, and satisfying $F(C\cdot W)=u_C^{-2}F(W)$ for every variable change $C$ with unit scaling factor $u_C$. Assume that the $q$-expansion of $F$, namely its value on the Tate curve over the Laurent series ring $\mathbb{Z}/M((q))$, is the image of a power series $g$ over $\mathbb{Z}/M$, i.e. has no polar part. The conclusion is that there exists $a\in\mathbb{Z}/M$ with $12a=0$ such that for every commutative $\mathbb{Z}/M$-algebra $A$ and every Weierstrass curve $W$ over $A$ with unit discriminant one has $F(W)=\mathrm{alg}(a)\cdot b_2(W)$, where $\mathrm{alg}$ is the structure map $\mathbb{Z}/M\to A$.
--
--   This is the classification, due to Mazur in his study of the Eisenstein ideal, of level-one weight-two modular forms modulo $M$ that are holomorphic at the cusp: they are exactly the multiples of the invariant $b_2$ by constants annihilated by $12$. It is assembled from the cases in which $6$ is invertible, the characteristic-zero case $M=0$, and the cases of prime-power moduli $2^e$ and $3^e$, and feeds the divisibility statement [`ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff`](thm.html#ModularForm.dvd_twelve_mul_qCoeff_zero_and_dvd_qCoeff_mul_of_dvd_qCoeff) on $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KatzModularForm_exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two.lean

import Definitions.Def_ModularForm_KatzLevelOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem KatzModularForm.exists_twelve_mul_eq_zero_and_toFun_eq_mul_b2_of_weight_two
    (M : ℕ) (F : KatzModularForm (ZMod M) 2) (g : PowerSeries (ZMod M))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod M) g) :
    ∃ a : ZMod M, 12 * a = 0 ∧ ∀ (A : Type) [CommRing A] [Algebra (ZMod M) A]
      (W : WeierstrassCurve A) (hW : IsUnit W.Δ),
      F.toFun W hW = algebraMap (ZMod M) A a * W.b₂ := by sorry
