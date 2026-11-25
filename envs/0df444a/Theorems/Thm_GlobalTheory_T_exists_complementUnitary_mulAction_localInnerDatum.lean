-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_complementUnitary_mulAction_localInnerDatum
-- name    : GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:19:41.507404+00:00
-- url     : https://prove2.me/theorems/bbc49823-ab1c-5342-af4e-f6e41da0c49c
-- title:
--   T: exists complement Unitary mul Action local Inner Datum
-- statement:
--   The T construction uses the exists complement Unitary mul Action local Inner Datum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatumStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatumStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatumStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by sorry
