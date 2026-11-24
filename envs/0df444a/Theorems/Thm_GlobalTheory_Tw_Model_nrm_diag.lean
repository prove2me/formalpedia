-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_nrm_diag
-- name    : GlobalTheory.Tw.Model.nrm_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:31.569953+00:00
-- url     : https://prove2.me/theorems/decb7a39-1658-4a43-bd6e-1440badcef57
-- title:
--   Model: nrm diag
-- statement:
--   The Model construction uses the nrm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L114-L117

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

theorem GlobalTheory.Tw.Model.nrm_diag : nrm (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1/2] := by sorry
