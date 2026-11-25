-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStabLat_cls_map
-- name    : GlobalTheory.HL.FrameStabLat.cls_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:20.568002+00:00
-- url     : https://prove2.me/theorems/e1236bff-38d9-4a3b-8e9b-9bc844e7cf5a
-- title:
--   Frame Stab Lat: cls map
-- statement:
--   The Frame Stab Lat construction uses the cls map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L200-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L200-L239

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.FrameStabLat.cls_map (S : Frames L r k) (g g' : Fin (r + 1) → S.V) (h : S.GLV)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (e : ∀ j, h (g j) = ∑ i, s i j • g i) (e' : ∀ j, h (g' j) = ∑ i, s' i j • g' i)
    (π : E) (hπ : π ∈ L.O) (hth : ∃ d ∈ L.O, π = algebraMap F E S.th * d)
    (c : ∀ i j, ∃ c ∈ L.O, s i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c)
    (c' : ∀ i j, ∃ c ∈ L.O, s' i j = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) i j + π * c) :
    ∀ p ∈ S.frameCls g g', h • p ∈ S.frameCls g g' := by sorry
