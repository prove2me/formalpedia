-- Prove2me | Theorems.Thm_ModularCurve_JH_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar
-- name    : ModularCurve.JH.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/45787dff-d865-5d21-921f-aa99d79e94f8
-- title:
--   Pull-back J_H(M)→ J₁(M) commutes with T_ℓ and ⟨ d⟩
-- statement:
--   Fix $M\ge 1$ (nonzero) and a subgroup $H\le(\mathbf Z/M\mathbf Z)^\times$. Assume the Hecke–diamond input packages [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58) (for every prime $\ell$ the predicate `HeckeInputsOneAlong` over $\overline{\mathbf Q}$ for level $M$ and $\ell$, and for every $d$ coprime to $M$ the existence of a diamond automorphism of the function field of $X_1(M)$ over $\mathbf Q$ together with a base change of it to $\overline{\mathbf Q}$) and [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113) (for every prime $\ell$ the predicate `HeckeInputsHAlong` over $\overline{\mathbf Q}$, and for every unit $d\in(\mathbf Z/M\mathbf Z)^\times$ the existence of an automorphism of $\overline{\mathbf Q}\cdot F(X_H(M))$ satisfying `IsDiamondAutHBar`), and assume that every nonzero element of $\overline{\mathbf Q}\cdot F(X_1(M))$ has a degree-zero divisor recording its orders at all places. Let $\iota$ be an $\overline{\mathbf Q}$-algebra map from $\overline{\mathbf Q}\cdot F(X_H(M))$ to $\overline{\mathbf Q}\cdot F(X_1(M))$ which is the identity on the underlying Laurent series, with $\iota$ integral and satisfying the fundamental identity `FundamentalIdentityAlong`, and let $\pi^\ast$ denote the induced pull-back map $J_H(M)=\mathrm{Pic}^0\to\mathrm{Pic}^0=J_1(M)$ on degree-zero divisor classes. The conclusion is a conjunction: first, for every prime $\ell\nmid M$ and every $x\in J_H(M)$, $\pi^\ast(T_\ell x)=T_\ell(\pi^\ast x)$, where the left-hand $T_\ell$ is `heckeOperatorHAlong` (the correspondence built from the `HeckeInputsHAlong` data, zero if those fail) and the right-hand one is `heckeOperatorOneBar`; second, for every natural number $d$ coprime to $M$ and every $x$, $\pi^\ast(\langle d\bmod M\rangle x)=\langle d\rangle(\pi^\ast x)$, the operators being the actions on divisor classes of the semilinear automorphisms attached to `diamondAutHBar M H` and `diamondAutBar M`.
--
--   This is the Hecke- and diamond-equivariance of pull-back along the forgetful covering $X_1(M)\to X_H(M)$, for primes $\ell$ prime to the level. It is used in the analysis of the Tate module of $J_1(M)$, in particular in the statements about degeneracy maps, old lattices and the diamond-fixed part used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_and_pullbackAlongHom_diamondHBar_eq_diamondOneBar
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M H)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ∀ x : ModularCurve.JH M H,
      AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) =
        ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x)) ∧

    (∀ (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JH M H),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI
          (ModularCurve.diamondHBar M H (ZMod.unitOfCoprime d hd) x) =
        ModularCurve.diamondOneBar M d (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x)) := by sorry
