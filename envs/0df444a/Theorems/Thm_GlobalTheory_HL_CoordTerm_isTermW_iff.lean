-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordTerm_isTermW_iff
-- name    : GlobalTheory.HL.CoordTerm.isTermW_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:24:24.688909+00:00
-- url     : https://prove2.me/theorems/12176354-5f0f-531d-b6c2-a2b3cebf0523
-- title:
--   Coord Term: is Term W iff
-- statement:
--   The Coord Term construction uses the is Term W iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverFrameCoordinates.lean#L183-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverFrameCoordinates.lean#L183-L283

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverFrameCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

theorem GlobalTheory.HL.CoordTerm.isTermW_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (d : LocNG.Datum P) (n n' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V), LocNG.IsTermOver P d ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ ∧ n ∈ P.A.N ∧ n' ∈ P.B.N ∧ Λ = LocNG.img n (P.A.LamStd d.L) ∧ Λ = LocNG.img n' (P.B.LamStd d.L') ↔ S.IsTermW (c.dat d) (c.lat Λ) (c.grp n) (c.grp n') := by sorry
