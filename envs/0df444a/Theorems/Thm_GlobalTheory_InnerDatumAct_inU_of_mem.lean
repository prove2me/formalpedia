-- Prove2me | Theorems.Thm_GlobalTheory_InnerDatumAct_inU_of_mem
-- name    : GlobalTheory.InnerDatumAct.inU_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:29.930449+00:00
-- url     : https://prove2.me/theorems/a030be6d-6a8c-5547-9fb6-da505e6bef20
-- title:
--   Inner Datum Act: in U of mem
-- statement:
--   The Inner Datum Act construction uses the in U of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean#L96-L108

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

theorem GlobalTheory.InnerDatumAct.inU_of_mem {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) : InU P g := by sorry
