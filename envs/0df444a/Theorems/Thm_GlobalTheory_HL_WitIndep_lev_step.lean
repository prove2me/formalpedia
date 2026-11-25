-- Prove2me | Theorems.Thm_GlobalTheory_HL_WitIndep_lev_step
-- name    : GlobalTheory.HL.WitIndep.lev_step
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:37:06.321479+00:00
-- url     : https://prove2.me/theorems/1b921396-5419-530c-ac7c-5d2183fbeb33
-- title:
--   Wit Indep: lev step
-- statement:
--   The Wit Indep construction uses the lev step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L102-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermInvariantsIndependentOfWitnesses.lean#L102-L125

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.WitIndep.lev_step {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') (b : S.V) (j : ℕ)
    (hb : ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • h i + ∑ i, al' i • h' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)) :
    ∃ al al' : Fin (r + 1) → E, b = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by sorry
