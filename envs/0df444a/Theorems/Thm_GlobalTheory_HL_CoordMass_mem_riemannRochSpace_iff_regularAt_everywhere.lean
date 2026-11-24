-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordMass_mem_riemannRochSpace_iff_regularAt_everywhere
-- name    : GlobalTheory.HL.CoordMass.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:24.27984+00:00
-- url     : https://prove2.me/theorems/b062fd73-08c0-45cb-80ee-a8153395bbf0
-- title:
--   Coord Mass: mem riemann Roch Space iff regular At everywhere
-- statement:
--   The Coord Mass construction uses the mem riemann Roch Space iff regular At everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportUnitaryMass.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportUnitaryMass.lean#L24-L41

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMass
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.CoordMass.mem_riemannRochSpace_iff_regularAt_everywhere (g : S.GLV) : g ∈ S.H0 ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
    ∀ b, g (S.f b) = S.f b ∧ g (S.f' b) = S.f' b := by sorry
