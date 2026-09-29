-- Prove2me | Theorems.Thm_ModularCurve_lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C
-- name    : ModularCurve.lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/6cb58ff5-d6db-51c0-aa23-3cabf6252b4c
-- title:
--   Diamond operators make the Igusa cover of X₁(M) Galois
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $\Omega$ be an algebraically closed field of characteristic $p$. Let $w$ be an integral weight-one form of level $M$ over $\Omega$, that is, a modular form of weight $1$ for $\Gamma_1(M)$ together with a power series over $\mathbb{Z}$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of the form and whose image `intSeriesC` in the Laurent series field $\Omega((q))$ is nonzero; write $a :=$ `w.hasseRootFn` for the inverse of that image, $K_0 :=$ `x1FunctionFieldC` $\Omega\,M$ for the intermediate field of $\Omega((q))$ generated over $\Omega$ by the set `intFormRatiosC` $\Omega\,(\Gamma_1(M))$, and $\mathrm{Ig} :=$ `igusaFunctionFieldX1C` $\Omega\,M\,w$ for the intermediate field generated over $\Omega$ by $K_0 \cup \{a\}$. Let $\delta$ be a diamond datum for these data: a monoid homomorphism `δ.act` from $(\mathbb{Z}/p)^\times$ to the group of $\Omega$-algebra automorphisms of $\mathrm{Ig}$, acting trivially on every element of $\mathrm{Ig}$ lying in $K_0$, and sending $a$ to $(\overline{b^{-1}}) \cdot a$, the scalar being the image of $b^{-1} \bmod p$ in $\Omega$. Then the fixed field of the image subgroup of `δ.act`, pushed forward into $\Omega((q))$, equals $K_0$; and, for the algebra structure on $\mathrm{Ig}$ over $K_0$ given by the inclusion $K_0 \le \mathrm{Ig}$, the extension $\mathrm{Ig}/K_0$ is Galois.
--
--   This identifies the Igusa cover of $X_1(M)$ in characteristic $p$ as a Galois extension of the function field of $X_1(M)$ with the diamond operators exhausting its Galois group, the analogue of the classical description of Igusa curves as $(\mathbb{Z}/p)^\times$-covers. It is used in the analysis of which functions fail to lie in the Igusa function field, as in [`ModularCurve.jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd`](thm.html#ModularCurve.jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C.lean

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

open CongruenceSubgroup AlgebraicCurve Polynomial
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.lift_fixedField_range_act_eq_x1FunctionFieldC_and_isGalois_igusaFunctionFieldX1C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M) (δ : ModularCurve.IgusaDiamondDataX1C Ω M w p) :
    IntermediateField.lift (IntermediateField.fixedField (MonoidHom.range δ.act)) = ModularCurve.x1FunctionFieldC Ω M ∧
    (letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    IsGalois ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w)) := by sorry
