-- Prove2me | Theorems.Thm_GlobalTheory_HL_DatumStab_inner_iff
-- name    : GlobalTheory.HL.DatumStab.inner_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:30:20.486491+00:00
-- url     : https://prove2.me/theorems/910743f8-12d2-5256-a606-bf4fcae6bd54
-- title:
--   Datum Stab: inner iff
-- statement:
--   The Datum Stab construction uses the inner iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DatumStabilizerBetweenLatticeStabilizers.lean#L65-L81

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

theorem GlobalTheory.HL.DatumStab.inner_iff (S : Frames L r k) {g : Fin (r + 1) → S.V} {A Λ₀ : Submodule L.O S.V} {n : S.GLV}
    (hn : n ∈ S.Nof g)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by sorry
