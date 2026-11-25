-- Prove2me | Theorems.Thm_GlobalTheory_InnerDatumAct_moves_one
-- name    : GlobalTheory.InnerDatumAct.moves_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:22.488715+00:00
-- url     : https://prove2.me/theorems/f4d808ed-cdab-427b-b36b-e0ea36b6fc85
-- title:
--   Inner Datum Act: moves one
-- statement:
--   The Inner Datum Act construction uses the moves one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L192-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L192-L196

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

theorem GlobalTheory.InnerDatumAct.moves_one {P : FPair H r} (d : Datum P) : Datum.Moves (1 : V ≃ₗ[E] V) d d := by sorry
