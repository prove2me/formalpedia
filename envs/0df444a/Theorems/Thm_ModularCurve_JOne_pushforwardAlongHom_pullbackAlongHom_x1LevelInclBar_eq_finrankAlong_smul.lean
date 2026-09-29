-- Prove2me | Theorems.Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
-- name    : ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/6d8d5ae1-daea-55ec-b986-c06ceaf42e0b
-- title:
--   Push–pull along the first degeneracy map is multiplication by degree
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $p$, and write $\bar{\mathbb Q}$ for `AlgebraicClosure ℚ`. Let $\alpha$ denote `x1LevelInclBar` for the divisibility $N \mid N p$, i.e. the $\bar{\mathbb Q}$-algebra map between the base-changed modular function fields $\bar{\mathbb Q}\cdot F(\Gamma_1(N)) \to \bar{\mathbb Q}\cdot F(\Gamma_1(Np))$ inside Laurent series given by the inclusion of intermediate fields, and let $\beta$ denote `x1LevelSubstBar` for $p$ and $Np \mid Np$. Assume: $p \nmid N$; that the function field of level $Np$ has principal divisors (every nonzero element has a degree-zero divisor of orders); that the ring homomorphisms underlying $\alpha$ and $\beta$ are integral; that the fundamental identity holds along each of them for the algebra structures they induce; that each makes the level-$Np$ field a finite module over the source field; and that the pushforward norm formula for divisors holds along each. The conclusion is that for every $x$ in $J_1(N) = \mathrm{Pic}^0(\bar{\mathbb Q}\cdot F(\Gamma_1(N)))$, the quotient of degree-zero divisors on places by principal divisors, the pushforward along $\alpha$ of the pullback along $\alpha$ of $x$ equals $\mathrm{finrankAlong}(\alpha) \cdot x$, where $\mathrm{finrankAlong}(\alpha)$ is the $\bar{\mathbb Q}\cdot F(\Gamma_1(N))$-module rank of $\bar{\mathbb Q}\cdot F(\Gamma_1(Np))$ via $\alpha$, viewed in $\mathbb Z$.
--
--   This is the standard push–pull relation $\alpha_*\alpha^* = \deg(\alpha)$ on the Jacobian $J_1(N)$ for the first of the two degeneracy maps $X_1(Np) \to X_1(N)$, in the function-field presentation of $\mathrm{Pic}^0$ used throughout. It is one of the degeneracy-map identities feeding the analysis of the kernel of $\alpha^* \oplus \beta^*$ on Tate modules, being cited in the proof that a class annihilated by the relevant pushforwards vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul.lean

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

theorem ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
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
          (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI x) =
        ((AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) : ℕ) : ℤ) • x := by sorry
