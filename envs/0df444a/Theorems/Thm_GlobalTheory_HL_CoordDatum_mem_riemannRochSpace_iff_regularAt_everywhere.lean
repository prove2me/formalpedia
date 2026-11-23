-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordDatum_mem_riemannRochSpace_iff_regularAt_everywhere
-- name    : GlobalTheory.HL.CoordDatum.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:18.089274+00:00
-- url     : https://prove2.me/theorems/28ced589-b652-41d0-a9d8-aa82f649716b
-- title:
--   Coord Datum: mem riemann Roch Space iff regular At everywhere
-- statement:
--   The Coord Datum construction uses the mem riemann Roch Space iff regular At everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L29-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFramePairCoordinatesTransportInnerData.lean#L29-L48

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

theorem GlobalTheory.HL.CoordDatum.mem_riemannRochSpace_iff_regularAt_everywhere (g : S.GLV) : g ∈ S.H0 ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
    ∀ b, g (S.f b) = S.f b ∧ g (S.f' b) = S.f' b := by sorry
