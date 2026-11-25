-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_quad_char_skew
-- name    : GlobalTheory.GramCount.quad_char_skew
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:54.024325+00:00
-- url     : https://prove2.me/theorems/228e887e-a7bf-5874-be46-c01fd1ef138d
-- title:
--   Gram Count: quad char skew
-- statement:
--   The Gram Count construction uses the quad char skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianQuadricAffineSubspaceResidueRing.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianQuadricAffineSubspaceResidueRing.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianQuadricAffineSubspaceResidueRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B] [Fintype B]
omit [Fintype B]

theorem GlobalTheory.GramCount.quad_char_skew (c : B →+* B) (hc : ∀ u, c (c u) = u) {ω : B} (hω : IsUnit (ω - c ω))
    (χ : AddChar B ℂ) (hχc : ∀ u, χ (c u) = χ u) {a w : B} (ha : c a = -a) (hw : c w = w) :
    χ (a * w) = 1 := by sorry
