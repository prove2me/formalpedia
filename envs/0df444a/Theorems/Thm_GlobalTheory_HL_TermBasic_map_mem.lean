-- Prove2me | Theorems.Thm_GlobalTheory_HL_TermBasic_map_mem
-- name    : GlobalTheory.HL.TermBasic.map_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:31:02.873097+00:00
-- url     : https://prove2.me/theorems/e1155765-9c12-404e-9743-408aa8dc30b8
-- title:
--   Term Basic: map mem
-- statement:
--   The Term Basic construction uses the map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetTermBasicFacts.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetTermBasicFacts.lean#L70-L79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TermBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg

theorem GlobalTheory.HL.TermBasic.map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {x : S.V} (hx : x ∈ S.spanTo g j) :
    n x ∈ S.spanTo g j := by sorry
