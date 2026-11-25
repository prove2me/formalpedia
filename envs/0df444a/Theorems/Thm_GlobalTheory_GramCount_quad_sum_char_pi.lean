-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_quad_sum_char_pi
-- name    : GlobalTheory.GramCount.quad_sum_char_pi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:28:22.081104+00:00
-- url     : https://prove2.me/theorems/626fa8f2-d52d-5071-a840-2617fbdc9fda
-- title:
--   Gram Count: quad sum char pi
-- statement:
--   The Gram Count construction uses the quad sum char pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianQuadricAffineSubspaceResidueRing.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianQuadricAffineSubspaceResidueRing.lean#L12-L29

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

theorem GlobalTheory.GramCount.quad_sum_char_pi (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {m : ℕ} (w : Fin m → B) :
    ∑ s : Fin m → B, χ (∑ i, s i * w i) =
      if w = 0 then (Fintype.card B : ℂ) ^ m else 0 := by sorry
