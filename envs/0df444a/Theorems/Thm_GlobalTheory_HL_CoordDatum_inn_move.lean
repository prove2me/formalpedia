-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordDatum_inn_move
-- name    : GlobalTheory.HL.CoordDatum.inn_move
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:59:47.730807+00:00
-- url     : https://prove2.me/theorems/6643bde2-c166-46de-9a84-3e87c55ed6d6
-- title:
--   Coord Datum: inn move
-- statement:
--   The Coord Datum construction uses the inn move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L119-L131

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

theorem GlobalTheory.HL.CoordDatum.inn_move (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V)
    (hp : ∀ v, g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f)) (L L' : Submodule M.L.O (H.Wb f)) :
    (∀ x y : ↥(H.perp (H.X f)), (y : V) = g x → (H.mkW f x ∈ L ↔ H.mkW f y ∈ L')) ↔
      c.grp g • c.inn f L = c.inn f L' := by sorry
