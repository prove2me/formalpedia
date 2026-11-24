-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_upper_mul_diag
-- name    : GlobalTheory.Reg.CellChange.upper_mul_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:28.777936+00:00
-- url     : https://prove2.me/theorems/4223f943-45f4-4d9d-922e-2a21e6f55646
-- title:
--   Cell Change: upper mul diag
-- statement:
--   The Cell Change construction uses the upper mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L74-L81

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

theorem GlobalTheory.Reg.CellChange.upper_mul_diag {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) (hb : b.BlockTriangular id)
    (hu : ∀ i, IsUnit (b i i)) (hc : c.BlockTriangular id) (hv : ∀ i, IsUnit (c i i)) (i : Fin n) :
    IsUnit ((b * c) i i) := by sorry
