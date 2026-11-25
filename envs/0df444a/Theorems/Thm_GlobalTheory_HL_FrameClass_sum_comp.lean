-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameClass_sum_comp
-- name    : GlobalTheory.HL.FrameClass.sum_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:17:29.397593+00:00
-- url     : https://prove2.me/theorems/9ff1708e-8a08-5cad-b306-4647ce216084
-- title:
--   Frame Class: sum comp
-- statement:
--   The Frame Class construction uses the sum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFrameClassProperties.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetFrameClassProperties.lean#L43-L49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass

theorem GlobalTheory.HL.FrameClass.sum_comp {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) E) (g p q : Fin n → V) (hp : ∀ j, p j = ∑ i, A i j • g i)
    (hq : ∀ j, q j = ∑ i, B i j • p i) (j : Fin n) : q j = ∑ i, (A * B) i j • g i := by sorry
