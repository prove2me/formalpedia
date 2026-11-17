-- Prove2me | Theorems.Thm_N25_cusp_middle_geometric_residue
-- name    : N25.cusp_middle_geometric_residue
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:11.268359+00:00
-- url     : https://prove2.me/theorems/78b93397-1c15-4d54-9cb5-dc6e270fc925
-- title:
--   A middle cusp has a primitive fifth root in its residue field
-- statement:
--   Fix an embedding $\iota:\overline{\mathbb Q}\hookrightarrow\mathbb C$ and a coefficientwise map $\kappa:F_{\overline{\mathbb Q}}\to F_{\mathbb C}$. Let a complex place $W$ lie over a geometric place $P$, with contraction and all orders preserved. Let $B\in\mathrm{SL}_2(\mathbb Z)$ have lower-left entry divisible by $5$ but not by $25$, assume membership in $\mathcal O_W$ is characterized by finite limits along $B\tau$, and assume a positive width $w$ gives nonzero normalized leading limits for every nonzero function. If $x\in F_{\mathbb Q}$ is the quotient of the element with series $j(q^{25})$ by $j_{25}$, then
--
--   $$x\in\mathcal O_P\quad\text{and}\quad\overline{x}\in k(P)\text{ is a primitive fifth root of unity}.$$
--
--   This residue calculation yields the degree lower bound for the width-$5$ cusp.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_N25_jqTwentyFive_mem_xH25
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve AlgebraicCurve N25.Endgame Filter Topology
open scoped MatrixGroups
open N25

theorem N25.cusp_middle_geometric_residue
    (ι : Qbar →+* ℂ) (κ : FG →+* laurentBaseChange ℂ FQ)
    (hκ : ∀ y : FG, (κ y : LaurentSeries ℂ) = coeffMap ι (y : LaurentSeries Qbar))
    (P : GPlace) (W : Place ℂ (laurentBaseChange ℂ FQ))
    (hcon : W.toValuationSubring.comap κ = P.toValuationSubring)
    (hord : ∀ y : FG, W.ord (κ y) = P.ord y)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hB5 : (5 : ℤ) ∣ B 1 0) (hB25 : ¬ (25 : ℤ) ∣ B 1 0)
    (hmem : ∀ y : laurentBaseChange ℂ FQ, y ∈ W.toValuationSubring ↔
      ∃ L : ℂ, Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (y : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds L))
    (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ FQ, y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (W.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L)) :
    let x : FQ := (⟨jqNModC ℚ 25,jqTwentyFive_mem_xH25 ℚ⟩ : FQ) / j25
    emb25 x ∈ P.toValuationSubring ∧ IsPrimitiveRoot (P.evalAt (emb25 x)) 5 := by sorry
