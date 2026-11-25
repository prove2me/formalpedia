-- Prove2me | Theorems.Thm_GlobalTheory_HermOrthBasis_exists_unit_norm
-- name    : GlobalTheory.HermOrthBasis.exists_unit_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:08.417802+00:00
-- url     : https://prove2.me/theorems/54248e0f-8e35-5f80-940f-8d98523bf8cb
-- title:
--   Herm Orth Basis: exists unit norm
-- statement:
--   The Herm Orth Basis construction uses the exists unit norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L97-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L97-L136

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HermOrthBasis.exists_unit_norm [CharZero F] (hH : IsHermND L Hm) {m : ℕ} (x : Fin m → Fin n → E)
    (hx : IsUnit (gramT L Hm x).det) (h : perp L Hm (Submodule.span E (Set.range x)) ≠ ⊥) :
    ∃ w ∈ perp L Hm (Submodule.span E (Set.range x)), IsUnit (hf L Hm w w) := by sorry
