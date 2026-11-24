-- Prove2me | Theorems.Thm_GlobalTheory_Frames_lowerTri_mul
-- name    : GlobalTheory.Frames.lowerTri_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:47.311059+00:00
-- url     : https://prove2.me/theorems/56eac5fb-e9c2-44eb-90c6-b05d87d8720b
-- title:
--   Frames: lower Tri mul
-- statement:
--   The Frames construction uses the lower Tri mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LowerTriIsUnitDet.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LowerTriIsUnitDet.lean#L20-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueFrameChangeByMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeByMatricesReflAndCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriangularMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LowerTriIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames
variable {S : Type} [CommRing S] {n : ℕ}

theorem GlobalTheory.Frames.lowerTri_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by sorry
