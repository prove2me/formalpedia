-- Prove2me | Theorems.Thm_GlobalTheory_T_frameLattice_trace_initialSpan_volume_eq
-- name    : GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:46:16.18+00:00
-- url     : https://prove2.me/theorems/011fb13e-576a-4583-b5c8-29a9ce61c2cf
-- title:
--   T: frame Lattice trace initial Span volume eq
-- statement:
--   The T construction uses the frame Lattice trace initial Span volume eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeTraceInitialSpanVolumeEqStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeTraceInitialSpanVolumeEqStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEqStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by sorry
