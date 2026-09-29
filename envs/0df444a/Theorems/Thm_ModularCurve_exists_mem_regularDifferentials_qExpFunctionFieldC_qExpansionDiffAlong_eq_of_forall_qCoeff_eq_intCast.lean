-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- name    : ModularCurve.exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ae5be152-bfba-5131-8e91-c177fcf630ba
-- title:
--   Integral weight-two cusp forms as regular differentials
-- statement:
--   Fix an algebraically closed field $k$ and a positive integer $M$ whose image in $k$ is nonzero, and let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ satisfy $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$. Let $f$ be a cusp form of weight $2$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$, and let $a:\mathbb N\to\mathbb Z$ be such that for every $n$ the $n$-th coefficient of the $q$-expansion of $f$ of period $1$ equals $a_n$ in $\mathbb C$. Write $F=$ [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $k((q))$ obtained by adjoining to $k$ all quotients $\mathrm{intSeriesC}\,k\,p_f/\mathrm{intSeriesC}\,k\,p_g$ with non-vanishing denominator, where $f,g$ are modular forms of a common weight on $\Gamma$ with integral $q$-expansions $p_f,p_g$ over $\mathbb Z$. The assertion is that there exists a Kähler differential $\omega\in\Omega[F/k]$ which is regular in the sense of [`AlgebraicCurve.regularDifferentials`](def/AlgebraicCurve_RegularDifferentials.html#L26), i.e. for every place $v$ of $F/k$ (a valuation subring of $F$, not all of $F$, containing the image of $k$ and a principal ideal ring) there is $h$ in that valuation subring with $\omega=h\cdot v.\mathrm{dCoord}$, $v.\mathrm{dCoord}=D_{k}(\text{uniformiser of }v)$, and such that the $q$-expansion of $\omega$ along the inclusion $F\hookrightarrow k((q))$ — the $k$-linear map `qExpansionDiffAlong`, determined when it exists by $D x\mapsto \mathrm{thetaL}(x)$ and $h\cdot\omega\mapsto h\,\mathrm{thetaL}$-twisted multiplication, and $0$ otherwise — equals the Laurent series attached to the power series $\sum_{n\ge 0}\bar a_n q^n$ with $\bar a_n$ the image of $a_n$ in $k$.
--
--   This is the $q$-expansion principle for weight-two cusp forms in the form used here: a weight-two cusp form on $\Gamma_H(M)$ with rational integral Fourier coefficients gives a differential, regular at every place, on the $q$-expansion function field of $X(\Gamma)$ over any algebraically closed field in which $M$ is invertible, with the reduced $q$-expansion $\sum a_n q^n$ (classically $f(q)\,dq/q$). It feeds the comparison of regular differentials on $X_1$-type curves with integral $q$-expansions used later in the modularity part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
    (k : Type*) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M] (hM : (M : k) ≠ 0)
    (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n = (a n : ℂ)) :
    ∃ ω ∈ AlgebraicCurve.regularDifferentials k ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ModularCurve.qExpansionDiffAlong (ModularCurve.qExpFunctionFieldC k Γ).val ω =
        HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k)) := by sorry
