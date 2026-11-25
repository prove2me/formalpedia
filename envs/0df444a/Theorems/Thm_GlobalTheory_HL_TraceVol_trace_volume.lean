-- Prove2me | Theorems.Thm_GlobalTheory_HL_TraceVol_trace_volume
-- name    : GlobalTheory.HL.TraceVol.trace_volume
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:43.195637+00:00
-- url     : https://prove2.me/theorems/885fb884-fe01-58d6-be60-f64c413b5d58
-- title:
--   Trace Vol: trace volume
-- statement:
--   The Trace Vol construction uses the trace volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeTraceInitialSpanVolumeEq.lean#L393-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeTraceInitialSpanVolumeEq.lean#L393-L412

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEq
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceVol
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.TraceVol.trace_volume : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by sorry
