-- Prove2me | Theorems.Thm_GlobalTheory_OrbitDenom_block_of
-- name    : GlobalTheory.OrbitDenom.block_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:22.285402+00:00
-- url     : https://prove2.me/theorems/cfe13664-50d7-4635-9378-29de7caaacd9
-- title:
--   Orbit Denom: block of
-- statement:
--   The Orbit Denom construction uses the block of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L288-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactors.lean#L288-L330

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
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
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]

theorem GlobalTheory.OrbitDenom.block_of : ∀ (bs : List (Eˣ × ℕ+)) (i : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    ∃ (l' l : ℕ) (t : E), l' ≤ i ∧ i < l ∧ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum ∧
      (∀ a b, l' ≤ a → a < l → l' ≤ b → b < l → sameBlock bs a b = true) ∧
      (∀ a b, l' ≤ a → a < l → ptEntryL bs a b = if a + b + 1 = l + l' then t else 0) ∧
      (∀ a b, l ≤ a → b < l → ptEntryL bs a b = 0) ∧ (∀ a b, l' ≤ a → b < l' → ptEntryL bs a b = 0)
  := by sorry
