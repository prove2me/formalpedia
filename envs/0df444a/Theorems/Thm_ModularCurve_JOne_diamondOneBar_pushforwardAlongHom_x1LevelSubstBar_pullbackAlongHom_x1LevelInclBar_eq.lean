-- Prove2me | Theorems.Thm_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
-- name    : ModularCurve.JOne.diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/dcb6858d-4dd2-5477-aa57-857408951f0e
-- title:
--   Diamond twist of mixed push–pulls on J₁(N)
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$, and write $L=\overline{\mathbb Q}$ (the `AlgebraicClosure` of $\mathbb Q$). Assume that the function field $L\cdot F(\Gamma_1(Np))$, namely `x1FunctionFieldBar (N*p)`, has principal divisors, i.e. every nonzero element of it is the datum of a degree-zero divisor recording its orders at all places over $L$. Consider the two $L$-algebra maps $L\cdot F(\Gamma_1(N))\to L\cdot F(\Gamma_1(Np))$: the degeneracy inclusion $\alpha=$ `x1LevelInclBar` attached to $N\mid Np$, and $\beta=$ `x1LevelSubstBar` at $p$ attached to $Np\mid Np$, the composite of `heckeBetaOneBar` with the inclusion `x1x0LevelInclBar`. Both are assumed to have integral underlying ring homomorphism, to satisfy the fundamental identity $\sum_{w\mid v}e_wf_w=[\,\cdot\,]$ along themselves, to make the target a finite module over the source for the induced algebra structure, and to satisfy the norm formula for pushforward of divisors. The conclusion is that for every class $x$ in $J_1(N)=\mathrm{Pic}^0(L\cdot F(\Gamma_1(N)))$ (degree-zero divisors modulo principal ones), the diamond endomorphism `diamondOneBar N p`, the action on $J_1(N)$ of the semilinear automorphism attached to the algebra automorphism `diamondAutBar N p`, satisfies $\langle p\rangle(\beta_*(\alpha^*x))=\alpha_*(\beta^*x)$, where $\alpha^*,\beta^*$ and $\alpha_*,\beta_*$ are the Picard pullbacks and pushforwards along $\alpha,\beta$ formed from the above witnesses.
--
--   This is the $X_1$-level comparison of the two mixed compositions of the degeneracy maps $X_1(Np)\rightrightarrows X_1(N)$ on Jacobians, the source of the relation $T_p^{*}=\langle p\rangle^{-1}T_p$; no degree factor occurs. It is used in the vanishing statement [`ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero`](thm.html#ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero) for the Tate module of $J_1(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq.lean

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

theorem ModularCurve.JOne.diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
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
      ModularCurve.diamondOneBar N p
          (AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβfin hβN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI x)) =
        AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαfin hαN
          (AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI x) := by sorry
