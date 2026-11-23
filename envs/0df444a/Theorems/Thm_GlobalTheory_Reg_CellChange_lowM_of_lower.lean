-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_of_lower
-- name    : GlobalTheory.Reg.CellChange.lowM_of_lower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:43.561006+00:00
-- url     : https://prove2.me/theorems/eaec0ac6-ed14-4159-9d86-6ba80c88ad1e
-- title:
--   Cell Change: low M of lower
-- statement:
--   The Cell Change construction uses the low M of lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L163-L171

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

theorem GlobalTheory.Reg.CellChange.lowM_of_lower (l : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) S) (τ : T)
    (h0 : ∀ i j, i < j → l τ i j = 0) (h1 : ∀ i, l τ i i = 1) :
    lowM (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) τ = l τ := by sorry
