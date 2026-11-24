-- Prove2me | Theorems.Thm_GlobalTheory_KS_EpsBundle_trivial_iff_coboundary
-- name    : GlobalTheory.KS.EpsBundle.trivial_iff_coboundary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:34.697861+00:00
-- url     : https://prove2.me/theorems/54196759-2e2d-4d20-b38a-f09eaa58c1a1
-- title:
--   Eps Bundle: trivial iff coboundary
-- statement:
--   The Eps Bundle construction uses the trivial iff coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L71-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L71-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle

theorem GlobalTheory.KS.EpsBundle.trivial_iff_coboundary : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (Q : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → ((∃ t : Q.Gen, t.IsGen) ↔ ∃ a : ∀ i, Γ(Y, j ⁻¹ᵁ Q.U i), ∀ i i', k i i' = resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i from fun _ hy => hy.1) (a i) - resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' from fun _ hy => hy.2) (a i')) := by sorry
