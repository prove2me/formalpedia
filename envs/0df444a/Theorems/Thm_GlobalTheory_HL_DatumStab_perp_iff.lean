-- Prove2me | Theorems.Thm_GlobalTheory_HL_DatumStab_perp_iff
-- name    : GlobalTheory.HL.DatumStab.perp_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:09:44.329752+00:00
-- url     : https://prove2.me/theorems/6ddf23e3-1280-5398-9d92-9602deb8668f
-- title:
--   Datum Stab: perp iff
-- statement:
--   The Datum Stab construction uses the perp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L37-L43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.DatumStab.perp_iff {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hg : g ∈ isomG L Hm) {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) :
    g x ∈ perp L Hm Y ↔ x ∈ perp L Hm Y := by sorry
