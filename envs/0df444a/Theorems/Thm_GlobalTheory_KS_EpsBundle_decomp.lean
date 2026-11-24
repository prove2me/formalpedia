-- Prove2me | Theorems.Thm_GlobalTheory_KS_EpsBundle_decomp
-- name    : GlobalTheory.KS.EpsBundle.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:40.138689+00:00
-- url     : https://prove2.me/theorems/1c125bba-9c7a-427c-9b8e-b17239fc8623
-- title:
--   Eps Bundle: decomp
-- statement:
--   The Eps Bundle construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TrivialIffCoboundary.lean#L31-L39

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

theorem GlobalTheory.KS.EpsBundle.decomp {Y Y' : Scheme.{0}} (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (O : Y.Opens)
    (H : ∀ F : Γ(Y', ρ ⁻¹ᵁ O), ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2)
    (W : Y'.Opens) (hW : ρ ⁻¹ᵁ O = W) (h : W ≤ ρ ⁻¹ᵁ O) (F : Γ(Y', W)) :
    ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.appLE O W h).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE O W h).hom ab.2 := by sorry
