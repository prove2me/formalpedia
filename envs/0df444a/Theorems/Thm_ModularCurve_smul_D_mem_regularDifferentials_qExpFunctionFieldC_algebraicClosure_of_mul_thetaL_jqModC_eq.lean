-- Prove2me | Theorems.Thm_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
-- name    : ModularCurve.smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/beea113f-2862-580d-88e9-6d9261943407
-- title:
--   Weight-two cusp forms give regular differentials x dj
-- statement:
--   Let $M\ge 1$ and let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup containing $\Gamma_1(M)$, and let $f$ be a cusp form of weight $2$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$. Let $a:\mathbb N\to\mathbb Z$ be such that for every $n$ the $n$-th coefficient of the width-one $q$-expansion of $f$ equals $a_n$ in $\mathbb C$. Write $F=$ [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) $(\overline{\mathbb Q},\Gamma)$ for the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the quotients of the integral $q$-expansion series of two modular forms of equal weight on $\Gamma$ (the denominator series being nonzero). Let $x,j\in F$, with $j$ equal, as a Laurent series, to $q^{-1}$ times the power series $E_4^3\cdot\eta^{-24}$ of [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15), and assume $x\cdot\theta(j)=\sum_{n\ge 0}a_nq^n$ in $\overline{\mathbb Q}((q))$, where $\theta=q\,d/dq$ is [`ModularCurve.thetaL`](def/ModularCurve_QExpansionDiff.html#L16). Then the Kähler differential $x\cdot d j\in\Omega_{F/\overline{\mathbb Q}}$ lies in [`AlgebraicCurve.regularDifferentials`](def/AlgebraicCurve_RegularDifferentials.html#L26): for every place $v$ of $F$ over $\overline{\mathbb Q}$ — a valuation subring of $F$, not all of $F$, containing $\overline{\mathbb Q}$ and a principal ideal ring — there is $g$ in that valuation subring with $x\,dj=g\,d\pi_v$ for the chosen uniformiser $\pi_v$.
--
--   This is the arithmetic form, over $\overline{\mathbb Q}$ and in terms of $q$-expansions, of the classical identification of weight-two cusp forms on $\Gamma$ with differentials of the first kind on the modular curve $X(\Gamma)$, under $f\mapsto 2\pi i f(\tau)\,d\tau=f(q)\,dq/q$. It is used to produce, from a weight-two cusp form with integral Fourier coefficients, a regular differential on the curve whose $q$-expansion along the cusp at infinity is the given series, a step in the construction feeding the Eichler–Shimura relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups

theorem ModularCurve.smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n = (a n : ℂ))
    (x j : ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hj : (j : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) *
        ModularCurve.thetaL (AlgebraicClosure ℚ) (ModularCurve.jqModC (AlgebraicClosure ℚ)) =
      HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ)
        (PowerSeries.mk fun n => (a n : AlgebraicClosure ℚ))) :
    x • KaehlerDifferential.D (AlgebraicClosure ℚ)
        ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) j ∈
      AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
        ↥(ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := by sorry
