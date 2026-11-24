-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizing_restrict_fromSpec_iff
-- name    : GlobalTheory.QCoh.isLocalizing_restrict_fromSpec_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:18.769818+00:00
-- url     : https://prove2.me/theorems/dfa6f48b-c775-4438-9157-d5fe29fe1ff7
-- title:
--   QCoh: is Localizing restrict from Spec iff
-- statement:
--   The QCoh construction uses the is Localizing restrict from Spec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L131-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L131-L172

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
variable (hU : IsAffineOpen U)

theorem GlobalTheory.QCoh.isLocalizing_restrict_fromSpec_iff :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)) ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by sorry
