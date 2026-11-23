-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_upper_inv
-- name    : GlobalTheory.Reg.CellChange.upper_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:34.054833+00:00
-- url     : https://prove2.me/theorems/35968b60-69ec-4b4d-b2c4-e1493fb87bf0
-- title:
--   Cell Change: upper inv
-- statement:
--   The Cell Change construction uses the upper inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L63-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix

theorem GlobalTheory.Reg.CellChange.upper_inv {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) : b⁻¹.BlockTriangular id ∧ (∀ i, IsUnit (b⁻¹ i i)) ∧ b * b⁻¹ = 1 := by sorry
