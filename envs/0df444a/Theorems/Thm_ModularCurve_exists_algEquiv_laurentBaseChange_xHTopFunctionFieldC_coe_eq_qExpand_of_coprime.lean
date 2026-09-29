-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
-- name    : ModularCurve.exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/30161530-efee-5a15-a32f-f52856e6f438
-- title:
--   Atkin–Lehner automorphism acting by q ↦ q^t
-- statement:
--   Fix a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a nonzero natural number $t$ with $\gcd(t,M)=1$. Write $\Gamma = \Gamma_H(M) \cap \Gamma_0(Mt)$, where $\Gamma_H(M)$ is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ formed by the matrices of $\Gamma_0(M)$ whose image under `gamma0Units M` lies in $H$, and let $F_0 =$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set [`ModularCurve.intFormRatiosC ℚ Γ`](def/ModularCurve_X1.html#L83). Let $E$ be the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_0$ under the coefficientwise map induced by $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$, and let $K \subseteq \overline{\mathbb{Q}}((q))$ be the corresponding field built in the same way from [`ModularCurve.xHFunctionFieldC ℚ M H`](def/ModularCurve_XH.html#L76). The assertion is that there is a $\overline{\mathbb{Q}}$-algebra automorphism $w$ of $E$ such that for every $x \in E$ whose underlying Laurent series lies in $K$, the Laurent series underlying $w(x)$ is the image of that of $x$ under [`ModularCurve.qExpand (AlgebraicClosure ℚ) t`](def/ModularCurve_X0.html#L25), the ring homomorphism multiplying all exponents by $t$, i.e. the substitution $q \mapsto q^t$. No claim is made about $w$ outside $K$.
--
--   This is the Atkin–Lehner operator $W_t$ at the exact divisor $t$ of the level $Mt$, realised on the function field with $q$-expansions at the cusp $\infty$, where it acts on functions of level $\Gamma_H(M)$ by $q \mapsto q^t$. It is used in the comparison of the function field of level $\Gamma_H(M) \cap \Gamma_0(Mt)$ with that of level $\Gamma_H(M)$, via [`ModularCurve.xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd`](thm.html#ModularCurve.xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ) [NeZero t] (htM : Nat.Coprime t M) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
      ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
        (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.xHFunctionFieldBar M H →
          ((w x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t))) :
              LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.qExpand (AlgebraicClosure ℚ) t (x : LaurentSeries (AlgebraicClosure ℚ)) := by sorry
