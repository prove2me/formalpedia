-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordMass_transport
-- name    : GlobalTheory.HL.CoordMass.transport
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:36.403087+00:00
-- url     : https://prove2.me/theorems/9aba7c36-594f-4732-9aa8-907e2648e042
-- title:
--   Coord Mass: transport
-- statement:
--   The Coord Mass construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportUnitaryMass.lean#L170-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportUnitaryMass.lean#L170-L346

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMass
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
open ValuativeRel
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.CoordMass.transport :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ) (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r),
      ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
        (∀ g, g ∈ P.UW0 ↔ c.grp g ∈ S.H0) ∧
          (∀ g, g ∈ P.K0 ↔ c.grp g ∈ S.K0) ∧
          Function.Bijective c.lat ∧
          (∀ g Λ, c.lat (_root_.Formalism.MainNotions.S.LocNG.img g Λ) =
            c.grp g • c.lat Λ) ∧
          (∀ g Λ, g ∈ _root_.Formalism.MainNotions.S.LocNG.Aut Λ ↔ c.grp g ∈
            MulAction.stabilizer S.GLV (c.lat Λ)) ∧
          ∀ t : _root_.Formalism.MainNotions.S.Loc.Term V M r, _root_.Formalism.MainNotions.S.LocNG.mu P t = S.mu (c.lat t.abelian₂) := by sorry
