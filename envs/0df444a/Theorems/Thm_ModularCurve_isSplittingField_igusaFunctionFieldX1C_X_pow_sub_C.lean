-- Prove2me | Theorems.Thm_ModularCurve_isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C
-- name    : ModularCurve.isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/677abf8c-1725-5797-b7ab-e80f5e88a187
-- title:
--   Igusa function field splits Xᵖ⁻¹-b over the X₁(M) field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $\Omega$ be an algebraically closed field of characteristic $p$. Let $w$ be an integral weight-one form of level $M$ over $\Omega$, that is, a weight-one modular form for $\Gamma_1(M)$ together with an integral power series whose image in $\mathbb{C}[[q]]$ is its $q$-expansion and whose reduction $\mathrm{intSeriesC}\,\Omega$ into $\mathrm{LaurentSeries}\,\Omega$ is nonzero; write $a = w.\mathrm{hasseRootFn} = (\mathrm{intSeriesC}\,\Omega\,w.\mathrm{series})^{-1}$. Let $K_0 = \mathrm{x1FunctionFieldC}\,\Omega\,M$ be the intermediate field of $\mathrm{LaurentSeries}\,\Omega$ obtained by adjoining to $\Omega$ the set $\mathrm{intFormRatiosC}\,\Omega\,(\Gamma_1(M))$, and let $\mathrm{Ig} = \mathrm{igusaFunctionFieldX1C}\,\Omega\,M\,w$ be the intermediate field generated over $\Omega$ by $K_0 \cup \{a\}$. Let $b \in K_0$ satisfy $b = a^{p-1}$ in $\mathrm{LaurentSeries}\,\Omega$. Then, for the $K_0$-algebra structure on $\mathrm{Ig}$ given by the inclusion $K_0 \le \mathrm{Ig}$, the field $\mathrm{Ig}$ is a splitting field of $X^{p-1} - b$ over $K_0$: this polynomial splits in $\mathrm{Ig}$ and its roots generate $\mathrm{Ig}$ over $K_0$.
--
--   The extension $\mathrm{Ig}/K_0$ is the Igusa (Hasse invariant) cover of the level-$M$ $q$-expansion function field presented as a Kummer extension of degree dividing $p-1$. Identifying it as a splitting field of $X^{p-1}-b$ makes the Kummer-extension ramification theory available; it is used in the genus inequality relating the genus of the base change of $X_1(M)$ to that of the Igusa cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open ModularCurve CongruenceSubgroup AlgebraicCurve Polynomial
open scoped MatrixGroups

theorem ModularCurve.isSplittingField_igusaFunctionFieldX1C_X_pow_sub_C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (b : ↥(ModularCurve.x1FunctionFieldC Ω M)) (hb : (b : LaurentSeries Ω) = w.hasseRootFn ^ (p - 1)) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    IsSplittingField ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w)
      (X ^ (p - 1) - C b) := by sorry
