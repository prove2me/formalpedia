-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_minors_iff
-- name    : GlobalTheory.Reg.CellChange.minors_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:57.683628+00:00
-- url     : https://prove2.me/theorems/bac5176d-7c4d-4bb0-a4a7-fb6e1c0bf606
-- title:
--   Cell Change: minors iff
-- statement:
--   The Cell Change construction uses the minors iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L57-L61

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

theorem GlobalTheory.Reg.CellChange.minors_iff {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    (∀ k (hk : k ≤ n), IsUnit (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) ↔
      ∃ u b : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b := by sorry
