-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_Top_mem_R_split
-- name    : GlobalTheory.SgLoc.Top.mem_R_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:54.707163+00:00
-- url     : https://prove2.me/theorems/86a0d501-2e1b-4711-9b66-81c599b2d7fe
-- title:
--   Top: mem R split
-- statement:
--   The Top construction uses the mem R split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L206-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures.lean#L206-L221

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]

theorem GlobalTheory.SgLoc.Top.mem_R_split (M : Model F E) (g : SplitG M.L) (hg : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.q ∣ a - b ∧ g.e x = ((a : F), (b : F)) := by sorry
