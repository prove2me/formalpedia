-- Prove2me | Theorems.Thm_GlobalTheory_HL_LatDet_card_quot_pow
-- name    : GlobalTheory.HL.LatDet.card_quot_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:44.813062+00:00
-- url     : https://prove2.me/theorems/b0019d9d-674e-4724-99bf-2f42e3b11b23
-- title:
--   Lat Det: card quot pow
-- statement:
--   The Lat Det construction uses the card quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelativeLatticeVolumeOfDetValuation.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelativeLatticeVolumeOfDetValuation.lean#L15-L22

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Theorems.Thm_GlobalTheory_CardQuotientPow_card_quot_pow

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatDet

theorem GlobalTheory.HL.LatDet.card_quot_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {p : R}
    (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by sorry
