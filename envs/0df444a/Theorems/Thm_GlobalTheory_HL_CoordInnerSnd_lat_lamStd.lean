-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordInnerSnd_lat_lamStd
-- name    : GlobalTheory.HL.CoordInnerSnd.lat_lamStd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:44.343023+00:00
-- url     : https://prove2.me/theorems/2532c126-cf42-42c7-b216-8797a378381b
-- title:
--   Coord Inner Snd: lat lam Std
-- statement:
--   The Coord Inner Snd construction uses the lat lam Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L305-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L305-L316

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
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
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)

theorem GlobalTheory.HL.CoordInnerSnd.lat_lamStd (hg : ∀ a, g a = c.e (Fr.f a)) (hgs : ∀ a, gs a = c.e (Fr.es a))
    (L : Submodule M.L.O (H.Wb Fr.f)) :
    c.lat (Fr.LamStd L) = S.stdLat g gs (c.inn Fr.f L) := by sorry
