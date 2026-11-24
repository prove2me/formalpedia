-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordInnerSnd_prim_iff
-- name    : GlobalTheory.HL.CoordInnerSnd.prim_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:01:14.745849+00:00
-- url     : https://prove2.me/theorems/b300039c-bc9b-40f6-a634-f249fc728d77
-- title:
--   Coord Inner Snd: prim iff
-- statement:
--   The Coord Inner Snd construction uses the prim iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L207-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean#L207-L258

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

theorem GlobalTheory.HL.CoordInnerSnd.prim_iff (hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O) (hpir : IsPrincipalIdealRing M.L.O)
    (hT : Fr.T ≠ 0) (L : Submodule M.L.O (H.Wb Fr.f))
    (hsd : ∀ x : ↥(H.perp (H.X Fr.f)),
      H.mkW Fr.f x ∈ L ↔ ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h x y ∈ M.L.O)
    (hz : H.mkW Fr.f ⟨Fr.z, z_perp Fr⟩ ∈ L) :
    (∀ (c : M.L.O) (y : ↥(H.perp (H.X Fr.f))), H.mkW Fr.f y ∈ L →
      H.mkW Fr.f ⟨Fr.z, z_perp Fr⟩ = (c : E) • H.mkW Fr.f y → IsUnit c) ↔
    ∃ y ∈ pre Fr L, H.h Fr.z y = 1 := by sorry
