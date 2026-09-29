-- Prove2me | Theorems.Thm_ModularCurve_finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one
-- name    : ModularCurve.finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/6c235362-77b3-566a-ab63-d381522f442e
-- title:
--   The Igusa function field has degree p-1 over X₁(M)
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $M \neq 0$, $5 \le M$ and $p \nmid M$. Let $\Omega$ be an algebraically closed field of characteristic $p$, and let $w$ be an `IntegralWeightOneForm` for $\Omega$ and $M$: a modular form of weight $1$ for $\Gamma_1(M)$ (viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$), together with a power series over $\mathbb{Z}$ whose image under $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of width $1$ of that form, subject to the requirement that the Laurent series `intSeriesC Ω w.series`, the image of the same integral series in $\Omega((q))$, is nonzero. Write $K_0 =$ `x1FunctionFieldC Ω M` for the intermediate field of $\Omega \subseteq \Omega((q))$ generated over $\Omega$ by the set `intFormRatiosC Ω (Gamma1 M)`, and let $a =$ `w.hasseRootFn` be the inverse in $\Omega((q))$ of `intSeriesC Ω w.series`. The Igusa field `igusaFunctionFieldX1C Ω M w` is the intermediate field generated over $\Omega$ by $K_0 \cup \{a\}$, so that it contains $K_0$; giving it the $K_0$-algebra structure coming from that inclusion, the assertion is that its $K_0$-rank is $p - 1$ (truncated subtraction in $\mathbb{N}$, so the value is $1$ when $p = 2$).
--
--   This is the degree of the Igusa cover of $X_1(M)$ in characteristic $p$, expressed on function fields: the extension obtained by adjoining the reciprocal of the reduced $q$-expansion of a weight-one form has degree exactly $p-1$. It supplies the degree input for the ramification and genus computations for Igusa curves, which in turn feed the genus-drop estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one.lean

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

theorem ModularCurve.finrank_x1FunctionFieldC_igusaFunctionFieldX1C_eq_sub_one
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    Module.finrank ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) = p - 1 := by sorry
