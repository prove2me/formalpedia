-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_det_embHom
-- name    : GlobalTheory.JR.Step.det_embHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:07.881919+00:00
-- url     : https://prove2.me/theorems/b12a1233-1cdb-49c3-9131-69c9103ea7ff
-- title:
--   Step: det emb Hom
-- statement:
--   The Step construction uses the det emb Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean#L83-L84

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
variable {r : ℕ} {k : Type} [CommRing k]

theorem GlobalTheory.JR.Step.det_embHom (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by sorry
