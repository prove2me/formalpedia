-- Prove2me | Theorems.Thm_GlobalTheory_CurvForm_form_mulVec_left
-- name    : GlobalTheory.CurvForm.form_mulVec_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:02.648113+00:00
-- url     : https://prove2.me/theorems/123d4797-75e4-4ebd-b70a-41c5fc4feba9
-- title:
--   Curv Form: form mul Vec left
-- statement:
--   The Curv Form construction uses the form mul Vec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNorm.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChernCurvatureFormSelfEqDualNorm.lean#L9-L12

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

theorem GlobalTheory.CurvForm.form_mulVec_left {g : ℕ} (K M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    form K (M *ᵥ v) w = form (Mᵀ * K) v w := by sorry
