-- Prove2me | Theorems.Thm_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
-- name    : ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/47d02928-a3ad-57a9-876c-c933fbf589fe
-- title:
--   Injectivity of the degeneracy Gram operator on TₚJ₁(N)
-- statement:
--   Fix natural numbers $N, M, p$ with $N$ and $M$ nonzero and $p$ prime, and assume $p \nmid N$, $N \mid M$, $N p \mid M$ and $M = N p$. Work over $K = \overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$) and assume that the function field $\overline{\mathbb Q}\,F(\Gamma_1(M))$, realised as the intermediate field [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182) of Laurent series over $\overline{\mathbb Q}$, has principal divisors, i.e. every nonzero element has a degree-zero divisor of orders at all places. Let $\alpha =$ `x1LevelInclBar` be the degeneracy embedding $\overline{\mathbb Q}\,F(\Gamma_1(N)) \hookrightarrow \overline{\mathbb Q}\,F(\Gamma_1(M))$ attached to $N \mid M$ (inclusion of intermediate fields), and let $\beta =$ `x1LevelSubstBar` be the embedding attached to $N p \mid M$, namely `heckeBetaOneBar` ($q \mapsto q^p$) followed by the level inclusion `x1x0LevelInclBar`. Assume of each of $\alpha, \beta$: that it is integral as a ring homomorphism; that the fundamental identity holds for the target viewed as an algebra over the source along it; that the target is a finite module over the source along it; and that the pushforward norm formula for divisors holds along it. Then for all $w_0, w_1$ in the Tate module $T_p J_1(N)$ — sequences $n \mapsto w_{i,n}$ in $J_1(N) = \mathrm{Pic}^0(\overline{\mathbb Q}, \overline{\mathbb Q}\,F(\Gamma_1(N)))$, the degree-zero divisor classes modulo principal divisors, satisfying $p^n \cdot w_{i,n} = 0$ and $p \cdot w_{i,n+1} = w_{i,n}$ — if for every $n$ both $\alpha_*\bigl(\alpha^* w_{0,n} + \beta^* w_{1,n}\bigr) = 0$ and $\beta_*\bigl(\alpha^* w_{0,n} + \beta^* w_{1,n}\bigr) = 0$, where $\alpha^*, \beta^*$ are `Pic0.pullbackAlongHom` and $\alpha_*, \beta_*$ are `Pic0.pushforwardAlongHom` at the given witnesses, then $w_0 = 0$ and $w_1 = 0$.
--
--   This is the old-injectivity statement for the pair of degeneracy maps $X_1(Np) \rightrightarrows X_1(N)$ with $p \nmid N$: the Gram operator $\begin{pmatrix} d & c\,T_p \\ \langle p\rangle^{-1}c\,T_p & d\end{pmatrix}$ built from the two degeneracy embeddings is injective on $T_pJ_1(N)^2$, the hypotheses being imposed levelwise on $p^n$-torsion while the conclusion is about Tate-module elements. It is used to deduce the corresponding statement for the degeneracy maps between Jacobians of the curves $X_H$, in [`ModularCurve.JH.tateModule_eq_zero_of_forall_pushforwardAlongHom_degeneracy_eq_zero`](thm.html#ModularCurve.JH.tateModule_eq_zero_of_forall_pushforwardAlongHom_degeneracy_eq_zero), which in turn supports the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.tateModule_eq_zero_of_forall_pushforwardAlongHom_x1LevelInclBar_x1LevelSubstBar_eq_zero
    (N M p : ℕ) [NeZero N] [NeZero M] [Fact p.Prime] (hpN : ¬ p ∣ N) (hNM : N ∣ M) (hNpM : N * p ∣ M) (hM : M = N * p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    (hαint : (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM).toRingHom.IsIntegral)
    (hβint : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM).toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM))
    (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM))
    (hαN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαfin)
    (hβN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβfin) :
    ∀ w₀ w₁ : TateModule p (ModularCurve.JOne N),
      (∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαfin hαN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0) →
      (∀ n : ℕ,
        AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβfin hβN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) hNM) hαint hαFI ((w₀ : ℕ → ModularCurve.JOne N) n) +
              AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p hNpM) hβint hβFI ((w₁ : ℕ → ModularCurve.JOne N) n)) = 0) →
      w₀ = 0 ∧ w₁ = 0 := by sorry
