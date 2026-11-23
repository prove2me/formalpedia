-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_entry_unit
-- name    : GlobalTheory.FrameBasic.entry_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:12.195878+00:00
-- url     : https://prove2.me/theorems/91af2caf-3ecf-4a67-bc3e-e9bbcc235dab
-- title:
--   Frame Basic: entry unit
-- statement:
--   The Frame Basic construction uses the entry unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L63-L77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem GlobalTheory.FrameBasic.entry_unit : ∀ (bs : List (Eˣ × ℕ+)) (a : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    sig bs a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ IsUnit (ptEntryL bs a (sig bs a))
  := by sorry
