-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordInnerSnd_transport
-- name    : GlobalTheory.HL.CoordInnerSnd.transport
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:16.872023+00:00
-- url     : https://prove2.me/theorems/11863962-989e-4061-bfcd-f03b216940de
-- title:
--   Coord Inner Snd: transport
-- statement:
--   The Coord Inner Snd construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L403-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L403-L411

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
import Theorems.Thm_GlobalTheory_HL_CoordUnip_transport

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordInnerSnd
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (Fr : LocNG.FrameD H r)

theorem GlobalTheory.HL.CoordInnerSnd.transport : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective (c.inn P.B.f) ∧ (∀ L, P.B.IsInner L ↔ S.IsInner S.f' S.es' (c.inn P.B.f L)) ∧ (∀ A, S.IsInner S.f' S.es' A → ∃ L, A = c.inn P.B.f L) ∧ ∀ L, c.lat (P.B.LamStd L) = S.stdLat S.f' S.es' (c.inn P.B.f L) := by sorry
