-- Prove2me | Theorems.Thm_GlobalTheory_InnerDatumAct_moves_unique
-- name    : GlobalTheory.InnerDatumAct.moves_unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:09.080803+00:00
-- url     : https://prove2.me/theorems/e632f2d4-0060-4186-bad1-ab7b88836173
-- title:
--   Inner Datum Act: moves unique
-- statement:
--   The Inner Datum Act construction uses the moves unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L170-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L170-L190

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.InnerDatumAct
open Formalism.MainNotions.S.LocNG
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem GlobalTheory.InnerDatumAct.moves_unique {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) {d d₁ d₂ : Datum P}
    (h₁ : Datum.Moves g d d₁) (h₂ : Datum.Moves g d d₂) : d₁ = d₂ := by sorry
