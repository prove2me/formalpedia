-- Prove2me | Theorems.Thm_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
-- name    : ModularCurve.JH.exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e312e896-5f67-5adf-ba56-db73569f07d4
-- title:
--   Pull-back and push-forward between J_H(M) and J₁(M)
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbf Z/M)^\times$, and assume [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58): for every prime $\ell$ the predicate `HeckeInputsOneAlong` holds over $\overline{\mathbf Q}$ at level $M$ and $\ell$, and for every $d$ coprime to $M$ there is a $\mathbf Q$-automorphism of the $q$-expansion function field `x1FunctionField M` satisfying `IsDiamondAut M d` together with an $\overline{\mathbf Q}$-automorphism of `x1FunctionFieldBar M` base-changed from it. Assume also that degree-zero divisors of nonzero functions exist on `x1FunctionFieldBar M`. Let $\iota$ be an $\overline{\mathbf Q}$-algebra map from `xHFunctionFieldBar M H` to `x1FunctionFieldBar M` which is the identity on underlying Laurent series, and let $S\subset\mathbf N$ be a finite set each of whose elements is coprime to $M$ and has unit class in $H$, such that reduction mod $M$ is a bijection $S\to H$. Then there are additive maps $\mathrm{pull}\colon J_H(M)\to J_1(M)$ and $\mathrm{push}\colon J_1(M)\to J_H(M)$ between the degree-zero divisor class groups, and integers $c,m>0$ with $cm=\#S$, such that: $\mathrm{pull}$ equals `Pic0.pullbackAlongHom` along $\iota$ for every witness of integrality and of `FundamentalIdentityAlong`; $\mathrm{push}$ equals `Pic0.pushforwardAlongHom` for every witness of integrality, `FiniteAlong` and `NormFormulaAlong`; both commute with the action of every $\sigma\in\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$; $\mathrm{push}\circ\mathrm{pull}=c\cdot\mathrm{id}$; each `diamondOneBar M d` with $d\in S$ fixes every element of the image of $\mathrm{pull}$; and $\sum_{d\in S}\langle d\rangle y=m\cdot\mathrm{pull}(\mathrm{push}\,y)$ for all $y\in J_1(M)$.
--
--   This packages the covering $X_1(M)\to X_H(M)$ on Jacobians: Galois-equivariant Picard pull-back and push-forward, the push-pull identity with multiplier the degree, and the diamond norm $\sum_{d\in S}\langle d\rangle$ as a multiple of pull-push, the degrees being constrained only by $cm=\#H$. It is used in the comparison of Tate modules of $J_H(M)$ and $J_1(M)$ and in the vanishing and inertia arguments feeding level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.exists_pullback_pushforward_jOne_galois_and_comp_eq_nsmul_and_sum_diamondOneBar_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))

    (S : Finset ℕ) (hS : ∀ d ∈ S, Nat.Coprime d M)
    (hSH : ∀ (d : ℕ) (hd : d ∈ S), ZMod.unitOfCoprime d (hS d hd) ∈ H)
    (hHS : ∀ h ∈ H, ∃! d : ℕ, d ∈ S ∧ (d : ZMod M) = ((h : (ZMod M)ˣ) : ZMod M)) :
    ∃ (pull : ModularCurve.JH M H →+ ModularCurve.JOne M)
      (push : ModularCurve.JOne M →+ ModularCurve.JH M H) (c m : ℕ),
      0 < c ∧ 0 < m ∧ c * m = S.card ∧

      (∀ (hint : ι.toRingHom.IsIntegral)
          (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
          (x : ModularCurve.JH M H),
        pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x) ∧
      (∀ (hint : ι.toRingHom.IsIntegral)
          (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
          (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
          (y : ModularCurve.JOne M),
        push y = AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JH M H),
        pull (σ • x) = σ • pull x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ModularCurve.JOne M),
        push (σ • y) = σ • push y) ∧

      (∀ x : ModularCurve.JH M H, push (pull x) = c • x) ∧

      (∀ d ∈ S, ∀ x : ModularCurve.JH M H,
        ModularCurve.diamondOneBar M d (pull x) = pull x) ∧

      (∀ y : ModularCurve.JOne M,
        ∑ d ∈ S, ModularCurve.diamondOneBar M d y = m • pull (push y)) := by sorry
