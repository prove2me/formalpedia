-- Prove2me | Theorems.Thm_GlobalTheory_KS_VertReg_exists_cramer
-- name    : GlobalTheory.KS.VertReg.exists_cramer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:36.03089+00:00
-- url     : https://prove2.me/theorems/eb134268-335e-4800-a7bd-27a677081830
-- title:
--   Vert Reg: exists cramer
-- statement:
--   The Vert Reg construction uses the exists cramer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LocDerRegularCoeff.lean#L91-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LocDerRegularCoeff.lean#L91-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertReg

theorem GlobalTheory.KS.VertReg.exists_cramer {Y : Scheme.{0}} {n : ℕ} (O₁ O₂ : Y.Opens) (J : Matrix (Fin n) (Fin n) Γ(Y, O₁))
    (e : Fin n → Γ(Y, O₂)) (a : Fin n) :
    ∃ c : Γ(Y, Y.basicOpen J.det ⊓ O₂), ∀ y : Sp ℂ ⟶ Y, ⊤ ≤ y ⁻¹ᵁ (Y.basicOpen J.det ⊓ O₂) → ∀ w : Fin n → ℂ,
      (∀ b, valAt' y O₂ (e b) = ∑ i, w i * valAt' y O₁ (J i b)) → valAt' y _ c = w a := by sorry
