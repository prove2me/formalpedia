-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_generic_minors
-- name    : GlobalTheory.Reg.CellChange.generic_minors
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:28.815806+00:00
-- url     : https://prove2.me/theorems/dcbf2b47-f78b-48ee-9f0d-8aaf127d75db
-- title:
--   Cell Change: generic minors
-- statement:
--   The Cell Change construction uses the generic minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L175-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L175-L192

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

theorem GlobalTheory.Reg.CellChange.generic_minors {κ T : Type} [Field κ] {r : T → ℕ} (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) (k : ℕ) (hk : k ≤ r τ) :
    (((A τ).map (algebraMap κ (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) *
      lowM MvPolynomial.X τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by sorry
