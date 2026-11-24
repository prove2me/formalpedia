-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_inv_glMap
-- name    : GlobalTheory.JR.Step.inv_glMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:48.899345+00:00
-- url     : https://prove2.me/theorems/bab43483-dd65-4047-92f4-40153084b5ee
-- title:
--   Step: inv gl Map
-- statement:
--   The Step construction uses the inv gl Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

theorem GlobalTheory.JR.Step.inv_glMap (Y : Gl r k) : inv (glMap φ Y) = (inv Y).map φ := by sorry
