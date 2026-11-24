-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_inv_diag
-- name    : GlobalTheory.Tw.Model.inv_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:25.787875+00:00
-- url     : https://prove2.me/theorems/c7f3c358-9001-4d88-a011-e616cc2b9406
-- title:
--   Model: inv diag
-- statement:
--   The Model construction uses the inv diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L110-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

theorem GlobalTheory.Tw.Model.inv_diag : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1/2, 0; 0, 1] := by sorry
