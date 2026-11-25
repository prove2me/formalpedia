-- Prove2me | Theorems.Thm_GlobalTheory_CurvForm_form_mulVec_right
-- name    : GlobalTheory.CurvForm.form_mulVec_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:15.725104+00:00
-- url     : https://prove2.me/theorems/4b1c2f44-1acb-4a1d-a132-0a0c8be04bbc
-- title:
--   Curv Form: form mul Vec right
-- statement:
--   The Curv Form construction uses the form mul Vec right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNorm.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNorm.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.CurvForm

theorem GlobalTheory.CurvForm.form_mulVec_right {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K v (M *ᵥ w) = form (K * Mᴴᵀ) v w := by sorry
