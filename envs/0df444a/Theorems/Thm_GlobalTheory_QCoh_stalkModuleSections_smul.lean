-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_stalkModuleSections_smul
-- name    : GlobalTheory.QCoh.stalkModuleSections_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:50.975737+00:00
-- url     : https://prove2.me/theorems/0b6100f6-3158-49cc-a83d-5d40ac5f582a
-- title:
--   QCoh: stalk Module Sections smul
-- statement:
--   The QCoh construction uses the stalk Module Sections smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L436-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L436-L437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

theorem GlobalTheory.QCoh.stalkModuleSections_smul (x : U) (r : Γ(X, U)) (t : (F.presheaf.stalk (x : X) :)) :
    r • t = X.presheaf.germ U x x.2 r • t := by sorry
