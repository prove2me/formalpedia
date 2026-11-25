-- Prove2me | Theorems.Thm_GlobalTheory_UnramCard_card_quot_map
-- name    : GlobalTheory.UnramCard.card_quot_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:50:14.385118+00:00
-- url     : https://prove2.me/theorems/9c6213b6-7f55-4ccf-b3bb-1a463d95e695
-- title:
--   Unram Card: card quot map
-- statement:
--   The Unram Card construction uses the card quot map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotEqPow.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotEqPow.lean#L28-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotEqPow
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
open GlobalTheory GlobalTheory.UnramCard

theorem GlobalTheory.UnramCard.card_quot_map {R : Type*} [CommRing R] (c : R ≃+* R) (a : R) :
    Nat.card (R ⧸ Ideal.span {c a}) = Nat.card (R ⧸ Ideal.span {a}) := by sorry
