-- Prove2me | Theorems.Thm_GlobalTheory_FrameLevel_lev_le_iff
-- name    : GlobalTheory.FrameLevel.lev_le_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:09.277933+00:00
-- url     : https://prove2.me/theorems/6aae92a8-51b3-45e5-a708-618b5d7a312a
-- title:
--   Frame Level: lev le iff
-- statement:
--   The Frame Level construction uses the lev le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFramesLevelLeIffCongrFlagSte.lean#L43-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFramesLevelLeIffCongrFlagSte.lean#L43-L132

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSte
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameLevel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FrameLevel.lev_le_iff {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    (y : S.V) (hy : y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) (j : ℕ) :
    S.lev g g' (algebraMap F E S.th • y) ≤ j ↔
      ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by sorry
