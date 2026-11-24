-- Prove2me | Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_Nof
-- name    : GlobalTheory.HL.CoordUnip.mem_Nof
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:07.80467+00:00
-- url     : https://prove2.me/theorems/4267af4b-e805-4afe-9327-1e7983523744
-- title:
--   Coord Unip: mem Nof
-- statement:
--   The Coord Unip construction uses the mem Nof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToZero.lean#L66-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanToZero.lean#L66-L93

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

theorem GlobalTheory.HL.CoordUnip.mem_Nof (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (g : S.GLV) :
    g ∈ S.Nof f ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
      (∀ j, j < r → ∀ v ∈ S.spanTo f (j + 1), g v - v ∈ S.spanTo f j) ∧
      ∀ v ∈ perp M.L S.Hm (S.spanTo f r), g v - v ∈ S.spanTo f r := by sorry
