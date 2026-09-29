-- Prove2me | Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
-- name    : ModularCurve.JOne.pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/0ea1853a-bdd5-531b-ae9f-244044029fb0
-- title:
--   α_{1,*}β₁^* equals deg(j)· Tₚ on J₁(N)
-- statement:
--   Fix $N \ge 1$ (as a `NeZero` instance) and a prime $p$ with $p \nmid N$, and assume that the function field $\overline{\mathbb Q}\cdot F(\Gamma_1(Np))$, realised as the intermediate field `x1FunctionFieldBar (N * p)` of Laurent series over $\overline{\mathbb Q}$, has principal divisors, i.e. every nonzero element has a divisor of degree $0$ recording its order at every place. Two degeneracy embeddings of $\overline{\mathbb Q}$-algebras into it are considered: $\alpha =$ `x1LevelInclBar`, the inclusion of $\overline{\mathbb Q}\cdot F(\Gamma_1(N))$ coming from $N \mid Np$, and $\beta =$ `x1LevelSubstBar`, the composite of `heckeBetaOneBar` with the inclusion `x1x0LevelInclBar` of the intermediate field attached to $\Gamma_1(N)\cap\Gamma_0(Np)$. The hypotheses are that both $\alpha$ and $\beta$ are integral ring homomorphisms, that each satisfies the fundamental identity $\sum_w e_w f_w = [F':F]$ over the corresponding field extension, that each makes the target a finite module over the source, and that each satisfies the pushforward norm formula for divisors. The conclusion is that for every $x$ in $J_1(N) = \mathrm{Pic}^0(\overline{\mathbb Q}\cdot F(\Gamma_1(N)))$ one has $\alpha_*(\beta^* x) = d \cdot T_p x$, where $\beta^*$ is `Pic0.pullbackAlongHom`, $\alpha_*$ is `Pic0.pushforwardAlongHom`, $T_p$ is `heckeOperatorOneBar N p` acting $\mathbb Z$-linearly on $J_1(N)$, and $d \in \mathbb Z$ is the image of the $\overline{\mathbb Q}$-module rank `finrankAlong` of `x1x0LevelInclBar` for $p$ and $N p \mid N p$, that is, the degree of $X_1(Np)$ over the intermediate curve.
--
--   This is the comparison of the composite of the two degeneracy maps between $J_1(N)$ and $J_1(Np)$ with the Hecke operator $T_p$ for $p \nmid N$: the composite is not $T_p$ itself but $T_p$ scaled by the degree of $X_1(Np)$ over the curve attached to $\Gamma_1(N)\cap\Gamma_0(Np)$, the factor arising because both degeneracy maps factor through that intermediate curve. It is used in the analysis of the $p$-old part of $J_1(Np)$, in particular in [`ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero`](thm.html#ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (N * p))]
    (hαint : (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)).toRingHom.IsIntegral)
    (hβint : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)))
    (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))))
    (hαN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαfin)
    (hβN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβfin) :
    ∀ x : ModularCurve.JOne N,
      AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαfin hαN
          (AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI x) =
        ((AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) •
          ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ x := by sorry
