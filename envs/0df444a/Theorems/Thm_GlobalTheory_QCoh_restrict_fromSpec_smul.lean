-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_restrict_fromSpec_smul
-- name    : GlobalTheory.QCoh.restrict_fromSpec_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:52.107639+00:00
-- url     : https://prove2.me/theorems/85acb521-0b21-4f9d-9215-a34e74c5c255
-- title:
--   QCoh: restrict from Spec smul
-- statement:
--   The QCoh construction uses the restrict from Spec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L123-L129

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

theorem GlobalTheory.QCoh.restrict_fromSpec_smul (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (s : Γ(F.restrict hU.fromSpec, W)) :
    (F.restrictAppIso hU.fromSpec W).hom (r • s) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r •
        (F.restrictAppIso hU.fromSpec W).hom s := by sorry
