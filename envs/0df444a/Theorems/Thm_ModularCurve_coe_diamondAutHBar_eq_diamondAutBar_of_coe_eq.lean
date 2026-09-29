-- Prove2me | Theorems.Thm_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
-- name    : ModularCurve.coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/bd7e6024-6352-57b3-adb9-d01d4f359aab
-- title:
--   Diamond automorphisms of X_H(M) and X₁(M) agree under ι
-- statement:
--   Fix a nonzero natural number $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$. Write $\overline{\mathbb{Q}}\cdot F_H$ for `xHFunctionFieldBar M H`, the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the rational function field `xHFunctionFieldC ℚ M H`, and similarly $\overline{\mathbb{Q}}\cdot F_1$ for `x1FunctionFieldBar M`. Assume `HeckeDiamondInputsAll M`, i.e. that for every prime $\ell$ the predicate `HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ` holds, and that for every $d$ coprime to $M$ there exists an automorphism of `x1FunctionField M` over $\mathbb{Q}$ satisfying `IsDiamondAut M d` and an automorphism of $\overline{\mathbb{Q}}\cdot F_1$ over $\overline{\mathbb{Q}}$ which is a base change, in the sense of `IsBaseChangeAutOf`, of `diamondAut M d`. Let $\iota : \overline{\mathbb{Q}}\cdot F_H \to \overline{\mathbb{Q}}\cdot F_1$ be a $\overline{\mathbb{Q}}$-algebra homomorphism which is the identity on underlying Laurent series: the Laurent series of $\iota(x)$ equals that of $x$ for all $x$. Then for every natural number $d$ coprime to $M$ and every $x \in \overline{\mathbb{Q}}\cdot F_H$, $$\iota\bigl(\langle d\rangle_H(x)\bigr) = \langle d\rangle_1\bigl(\iota(x)\bigr),$$ where $\langle d\rangle_H$ is `diamondAutHBar M H` evaluated at the unit class of $d$ in $(\mathbb{Z}/M)^\times$ (the automorphism chosen to satisfy `IsDiamondAutHBar`, the slash identity on quotients $f/g$ of $\Gamma_H(M)$-forms with integral $q$-expansions, and the identity otherwise) and $\langle d\rangle_1$ is `diamondAutBar M d`, the base change to $\overline{\mathbb{Q}}$ of the diamond automorphism `diamondAut M d` of `x1FunctionField M`.
--
--   This is the compatibility of the diamond operators $\langle d\rangle$ with the forgetful map $X_1(M) \to X_H(M)$, expressed on function fields over $\overline{\mathbb{Q}}$: both automorphisms are pinned down by the same slash identity on generators $f/g$, and a $\Gamma_H(M)$-form is a $\Gamma_1(M)$-form. It feeds the comparison of the Hecke and diamond actions on the Jacobians $J_H(M)$ and $J_1(M)$ under pullback along this map; the existence of the diamond automorphisms on the $X_H$ side is supplied by [`ModularCurve.heckeDiamondInputsHAll`](thm.html#ModularCurve.heckeDiamondInputsHAll).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))
    (d : ℕ) (hd : Nat.Coprime d M) (x : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    ι (ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime d hd) x) =
      ModularCurve.diamondAutBar M d (ι x) := by sorry
