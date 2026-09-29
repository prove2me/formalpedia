-- Prove2me | Theorems.Thm_ModularCurve_infinite_place_modularFunctionFieldBar
-- name    : ModularCurve.infinite_place_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4d740e7f-6d84-545e-b2c3-2a282528e9f1
-- title:
--   Infinitely many places on X₀(N) over ℚ̄
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Write $\overline{\mathbb Q}$ for `AlgebraicClosure ℚ` and let $\overline{F}_N :=$ `modularFunctionFieldBar N` be the intermediate field of the Laurent series field $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ obtained as `laurentBaseChange`, i.e. the subfield generated over $\overline{\mathbb Q}$ by the image, under the coefficientwise embedding `coeffEmb` of $\mathbb Q((q))$ into $\overline{\mathbb Q}((q))$, of `modularFunctionFieldFull N`, the latter being the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the family `divisorExpansions N`. A place of $\overline{F}_N$ over $\overline{\mathbb Q}$, in the sense of the project structure `Place`, consists of a valuation subring of $\overline{F}_N$ that contains the image of $\overline{\mathbb Q}$, is not the whole field, and is a principal ideal ring. The theorem asserts that the type of such places is infinite, i.e. `Infinite (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))`.
--
--   This records that the function field of $X_0(N)$ over $\overline{\mathbb Q}$, presented through $q$-expansions, carries infinitely many places, so that arbitrarily large finite sets of auxiliary places avoiding any prescribed finite set can be chosen. It is used in the height and mass estimates on $X_0(N)$, namely by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_infinite_place_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.infinite_place_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    Infinite (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by sorry
