-- Prove2me | Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul
-- name    : ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/2188ed5b-e6f3-5113-89e8-cb6ea3f859d5
-- title:
--   Push–pull along the degeneracy map β₁ is degree multiplication
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\nmid N$. Write $\bar{\mathbb Q}$ for `AlgebraicClosure ℚ` and, for a level $M$, let `x1FunctionFieldBar M` be the base change to $\bar{\mathbb Q}$, inside Laurent series over $\bar{\mathbb Q}$, of the function field of $X_1(M)$; `JOne N` is the group `Pic0` of that field over $\bar{\mathbb Q}$, i.e. degree-zero divisors on the places (valuation subrings containing $\bar{\mathbb Q}$, proper, with principal ideal ring) modulo principal divisors. Assume that the level-$Np$ field has the property that every nonzero element has a divisor recording its orders and of degree $0$. Two $\bar{\mathbb Q}$-algebra maps from level $N$ to level $Np$ are considered: the inclusion $\alpha$ = `x1LevelInclBar` attached to $N\mid Np$, and $\beta$ = `x1LevelSubstBar` with parameter $p$ attached to $Np\mid Np$, namely `heckeBetaOneBar` followed by `x1x0LevelInclBar`. For each of $\alpha$ and $\beta$ the hypotheses are: integrality of the underlying ring map, the fundamental identity along the map, finiteness of the target as a module over the source along the map, and the pushforward norm formula. The conclusion is that for every $x\in$ `JOne N`, the pushforward along $\beta$ of the pullback along $\beta$ of $x$ equals $\bigl(\operatorname{finrankAlong}\beta\bigr)\cdot x$, where $\operatorname{finrankAlong}\beta$ is the rank of the level-$Np$ field as a module over the level-$N$ field along $\beta$. The proof uses neither $p\nmid N$ nor any of the four hypotheses on $\alpha$.
--
--   This is the push–pull relation $\beta_{1,*}\beta_1^{*}=\deg(\beta_1)$ on $J_1(N)$ for the second degeneracy map $X_1(Np)\to X_1(N)$ ($\tau\mapsto p\tau$), the companion of the analogous relation for the inclusion leg. It is used in the level-lowering part of the argument, where the combination of the two degeneracy legs on $J_1(N)$ and $J_1(Np)$ is analysed, and is cited in the vanishing criterion for Tate modules expressed through the degeneracy pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul.lean

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

theorem ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul
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
      AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβfin hβN
          (AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI x) =
        ((AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) • x := by sorry
