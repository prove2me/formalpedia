-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_NSet
-- name    : GlobalTheory.HL.CoordUnip.mem_NSet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:59:53.881329+00:00
-- url     : https://prove2.me/theorems/7a918eef-0617-4977-b018-8bf829ca86c4
-- title:
--   Coord Unip: mem NSet
-- statement:
--   The Coord Unip construction uses the mem NSet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToZero.lean#L140-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToZero.lean#L140-L181

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)

theorem GlobalTheory.HL.CoordUnip.mem_NSet (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a))
    (g : V ≃ₗ[E] V) (g' : S.GLV) (hg : ∀ v, g' (e v) = e (g v)) :
    g ∈ Fr.NSet ↔ g' ∈ S.Nof f := by sorry
