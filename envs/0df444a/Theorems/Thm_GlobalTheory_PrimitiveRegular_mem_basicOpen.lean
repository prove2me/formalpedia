-- Prove2me | Theorems.Thm_GlobalTheory_PrimitiveRegular_mem_basicOpen
-- name    : GlobalTheory.PrimitiveRegular.mem_basicOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:17.531288+00:00
-- url     : https://prove2.me/theorems/607419b3-2741-5120-bee2-b6d8b285d795
-- title:
--   Primitive Regular: mem basic Open
-- statement:
--   The Primitive Regular construction uses the mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PrimitiveRegularOnSectionNonzeroLocus.lean#L33-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
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
open GlobalTheory GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem GlobalTheory.PrimitiveRegular.mem_basicOpen (u : HolUnif A L g) {n : ℕ} {σ : (lbPow L n).Sec} {θ : (Fin g → ℂ) → ℂ}
    (hθ : u.IsFnPow n σ θ) (k : (lbPow L n).ι) (z : Fin g → ℂ) (hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k)
    (hz : θ z ≠ 0) : valAt' (u.ex z).left ((lbPow L n).U k) (σ.f k) ≠ 0 := by sorry
