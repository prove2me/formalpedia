-- Prove2me | Theorems.Thm_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
-- name    : ModularCurve.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/666a97a6-3fc9-5d98-8ed4-693356860bb3
-- title:
--   Pull-back to X₁(M) intertwines U_q for q ∣ M
-- statement:
--   Fix $M \ge 1$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume the hypothesis `HeckeDiamondInputsAll M`, which asserts both that the predicate `HeckeInputsOneAlong` holds over $\overline{\mathbb{Q}}$ at level $M$ for every prime $\ell$, and that for every $d$ coprime to $M$ there is an automorphism of the level-$M$ function field over $\mathbb{Q}$ satisfying `IsDiamondAut` for $d$ together with an automorphism of its base change to $\overline{\mathbb{Q}}$ that is a base change of the former. Assume also that every nonzero element of the $\overline{\mathbb{Q}}$-field $\overline{\mathbb{Q}}\cdot F(\Gamma_1(M))$ (a subfield of Laurent series, `x1FunctionFieldBar M`) has a divisor recording its orders at all places and of degree $0$. Let $\iota$ be an $\overline{\mathbb{Q}}$-algebra map from $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ to $\overline{\mathbb{Q}}\cdot F(\Gamma_1(M))$ which is the identity on the underlying Laurent series, i.e. on $q$-expansions; assume $\iota$ is integral and satisfies the fundamental identity along $\iota$: for each place $v$ of the source, $\sum_{w \mid v} e(w)\deg(w) = [\overline{\mathbb{Q}}\cdot F(\Gamma_1(M)) : \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))]\deg(v)$. Let $q$ be a prime dividing $M$ and $x$ a class in $\mathrm{Pic}^0$ (degree-zero divisors modulo principal divisors) of $\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$. Then the pull-back along $\iota$ of $\mathrm{heckeOperatorHAlong}_q(x)$ equals $\mathrm{heckeOperatorOneBar}_q$ applied to the pull-back of $x$.
--
--   This is the compatibility of the Hecke correspondence $U_q$, for $q \mid M$, with the forgetful map $J_H(M) \to J_1(M)$ on $\overline{\mathbb{Q}}$-points, both operators being realised as $\alpha_*\beta^*$ through the appropriate $\Gamma_0(Mq)$-roof. It feeds the study of the Hecke and diamond action on $J_1(M)$, in particular the results on degeneracy maps, inertia augmentation and the toric and old lattices in the Tate module of $J_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
    (x : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) :
    AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI
        (haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q x) =
      ModularCurve.heckeOperatorOneBar M ⟨q, hq⟩ (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x) := by sorry
