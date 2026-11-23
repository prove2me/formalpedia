-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_map
-- name    : GlobalTheory.Reg.CellChange.lowM_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:46.487043+00:00
-- url     : https://prove2.me/theorems/b68ff9e1-f1d1-4680-a8e8-1bdd0917aac5
-- title:
--   Cell Change: low M map
-- statement:
--   The Cell Change construction uses the low M map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L157-L161

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
variable {T S S' : Type} [CommRing S] [CommRing S'] {r : T → ℕ}

theorem GlobalTheory.Reg.CellChange.lowM_map (f : S →+* S') (x : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → S) (τ : T) :
    (lowM x τ).map f = lowM (fun v => f (x v)) τ := by sorry
