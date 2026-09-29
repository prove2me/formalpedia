-- Prove2me | Theorems.Thm_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
-- name    : ModularCurve.JH.pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/b47fa1aa-c678-5afd-87d4-8f61c9f9c931
-- title:
--   Forgetful pull-backs commute with the two degeneracy pull-backs
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $M/p$ nonzero, and let $H \le (\mathbf{Z}/M)^\times$ be a subgroup, with $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) its image in $(\mathbf{Z}/(M/p))^\times$ under the reduction map on units. Assume the predicate [`ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p`](def/ModularCurve_X1DegeneracyPullback.html#L109), i.e. that $(M/p)\cdot p \mid M$, that `HeckeBetaOneDefined` holds for these data, that the two level maps `x1LevelInclBar` and `x1LevelSubstBar` over $\overline{\mathbf{Q}}$ are integral and satisfy the fundamental identity, and that principal divisors exist on the function field of $X_1(M)$; assume also `HasPrincipalDivisors` over $\overline{\mathbf{Q}}$ for the $q$-expansion function fields `x1FunctionFieldBar M`, `x1FunctionFieldBar (M / p)` and `xHFunctionFieldBar M H` (each a `HasPrincipalDivisors` instance: every nonzero element has a divisor of degree $0$ recording its orders at all places). Let $\iota$ be an $\overline{\mathbf{Q}}$-algebra map from `xHFunctionFieldBar M H` to `x1FunctionFieldBar M` which is the identity on underlying Laurent series, integral, and satisfying `FundamentalIdentityAlong`; let $\iota'$ be the analogous map at level $M/p$ for $H'$. Let $\alpha_H, \beta_H$ be $\overline{\mathbf{Q}}$-algebra maps from `xHFunctionFieldBar (M / p) H'` to `xHFunctionFieldBar M H`, integral and satisfying `FundamentalIdentityAlong`, with $\alpha_H$ the identity on Laurent series and $\beta_H$ acting as [`ModularCurve.qExpand (AlgebraicClosure ℚ) p`](def/ModularCurve_X0.html#L25), the ring map rescaling the exponent support by $p$. Then for every $x$ in `JH (M / p) H'`, the group $\mathrm{Pic}^0$ of degree-zero divisor classes of `xHFunctionFieldBar (M / p) H'`, the conorm pull-back along $\alpha_H$ followed by that along $\iota$ equals [`ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 0`](def/ModularCurve_X1DegeneracyPullback.html#L120) applied to the pull-back of $x$ along $\iota'$, and likewise with $\beta_H$ in place of $\alpha_H$ and the index $1$ in place of $0$.
--
--   This is the commutativity, for Picard functoriality, of the two squares formed by the coverings $X_1(M) \to X_H(M)$ and $X_1(M/p) \to X_{H'}(M/p)$ together with the degeneracy maps $X_H(M) \rightrightarrows X_{H'}(M/p)$ and $X_1(M) \rightrightarrows X_1(M/p)$: the forgetful pull-backs $J_H \to J_1$ intertwine the degeneracy pull-backs at the two levels. It is used in the study of the Tate module of $J_1$ and of images of degeneracy maps, notably in the statements about inertia and diamond operators on Tate modules cited further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1DegeneracyPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.pullbackAlongHom_pullbackAlongHom_eq_degeneracyPullbackPair_pullbackAlongHom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hdeg : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.JOne.DegeneracyPullbackInputs (M / p) M p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M / p))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ u, ((ι u : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hιint : ι.toRingHom.IsIntegral)
    (hιFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hιint)
    (ι' : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.x1FunctionFieldBar (M / p)))
    (hι' : ∀ u, ((ι' u : ↥(ModularCurve.x1FunctionFieldBar (M / p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι'int : ι'.toRingHom.IsIntegral)
    (hι'FI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι' hι'int)

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.xHFunctionFieldBar M H))
    (hα : ∀ u, ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u, ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβint) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom αH hαint hαFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 0
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) ∧
    (∀ x : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM),
      AlgebraicCurve.Pic0.pullbackAlongHom ι hιint hιFI (AlgebraicCurve.Pic0.pullbackAlongHom βH hβint hβFI x) =
        ModularCurve.JOne.degeneracyPullbackPair (M / p) M p 1
          (AlgebraicCurve.Pic0.pullbackAlongHom ι' hι'int hι'FI x)) := by sorry
