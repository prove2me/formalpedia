-- Prove2me | Theorems.Thm_ModularCurve_sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong
-- name    : ModularCurve.sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/456f297d-78b7-5d0e-89bf-a465e22ba3d9
-- title:
--   Diamond sum on divisors as pull-back of push-forward
-- statement:
--   Fix natural numbers $M₀$ (nonzero) and $t$ with $\gcd(M₀,t)=1$, and put $M=M₀t$. Assume that for every $d$ coprime to $M$ there is a $\mathbb Q$-automorphism $\sigma_0$ of [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137) (the intermediate field of $\mathbb Q$ in $\mathbb Q((q))$ cut out by $q$-expansions of level $\Gamma_1(M)$) satisfying `IsDiamondAut M d`, i.e. $\sigma_0$ sends a quotient $f/g$ of integral $q$-expansions of weight-$k$ modular forms on $\Gamma_1(M)$ to $(f|_k\gamma)/(g|_k\gamma)$ for any $\gamma\in\Gamma_0(M)$ with upper-left entry $\equiv d \pmod M$, and that `diamondAut M d` admits a base-change automorphism $\sigma'$ of `x1FunctionFieldBar M` over $\overline{\mathbb Q}$, that is, one agreeing with it on coefficientwise images of elements of `x1FunctionField M`, where `x1FunctionFieldBar M` is the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by those images. Assume that every nonzero element of `x1FunctionFieldBar M` has a degree-zero principal divisor. Let $\iota$ be an $\overline{\mathbb Q}$-algebra map from the base change to $\overline{\mathbb Q}$ of `x1x0FunctionFieldC ℚ M₀ t`, the $q$-expansion function field of $\Gamma_1(M₀)\cap\Gamma_0(t)$, into `x1FunctionFieldBar M`, which is the identity on underlying Laurent series and is integral, and let $D$ be a divisor on `x1FunctionFieldBar M` over $\overline{\mathbb Q}$. Then the sum, over $d<M$ with $\gcd(d,M)=1$ and $d\equiv 1\pmod{M₀}$, of the translates of $D$ by the semilinear automorphisms attached to `diamondAutBar M d` equals the pull-back along $\iota$ of the push-forward along $\iota$ of $D$, multiplied by the number of such $d$ for which `diamondAutBar M d` is the identity.
--
--   This is the statement that $X_1(M₀t) \to X(\Gamma_1(M₀)\cap\Gamma_0(t))$ is Galois with deck group acting through the diamond operators $\langle d\rangle$ with $d\equiv 1 \pmod{M₀}$, expressed on divisors over $\overline{\mathbb Q}$: the sum of the diamond translates is the norm, i.e. pull-back after push-forward, with multiplicity the order of the kernel of the diamond action. It is used in the analysis of the Jacobian $J_1$, namely in the identities for Frobenius elements and for elements of the inertia subgroup in terms of sums of diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.sum_diamondAutBar_smul_eq_ncard_smul_pullbackAlong_pushforwardAlong
    (M₀ t : ℕ) [NeZero M₀] (hM₀t : Nat.Coprime M₀ t)
    (hdia : ∀ d : ℕ, Nat.Coprime d (M₀ * t) →
      (∃ σ₀ : ModularCurve.x1FunctionField (M₀ * t) ≃ₐ[ℚ] ModularCurve.x1FunctionField (M₀ * t),
          ModularCurve.IsDiamondAut (M₀ * t) d σ₀) ∧
        ∃ σ' : ModularCurve.x1FunctionFieldBar (M₀ * t) ≃ₐ[AlgebraicClosure ℚ]
            ModularCurve.x1FunctionFieldBar (M₀ * t),
          ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ)
            (ModularCurve.diamondAut (M₀ * t) d) σ')
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M₀ * t))]
    (ι : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ t)
      →ₐ[AlgebraicClosure ℚ] ModularCurve.x1FunctionFieldBar (M₀ * t))
    (hι : ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ t),
      ((ι x : ModularCurve.x1FunctionFieldBar (M₀ * t)) : LaurentSeries (AlgebraicClosure ℚ))
        = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M₀ * t))) :
    ∑ d ∈ (Finset.range (M₀ * t)).filter (fun d => Nat.Coprime d (M₀ * t) ∧ d ≡ 1 [MOD M₀]),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M₀ * t) d) • D
      = Set.ncard {d : ℕ | d < M₀ * t ∧ Nat.Coprime d (M₀ * t) ∧ d ≡ 1 [MOD M₀] ∧
            ModularCurve.diamondAutBar (M₀ * t) d = AlgEquiv.refl} •
        AlgebraicCurve.Divisor.pullbackAlong ι hint (AlgebraicCurve.Divisor.pushforwardAlong ι hint D) := by sorry
