-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen_iff
-- name    : GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:37.455843+00:00
-- url     : https://prove2.me/theorems/10619702-6a76-4f0c-836d-ed604fde0709
-- title:
--   QCoh: is Localized Module res Basic Open iff
-- statement:
--   The QCoh construction uses the is Localized Module res Basic Open iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L80-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L80-L102

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

theorem GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) ↔
      (∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
          F.presheaf.map (homOfLE (X.basicOpen_le f)).op t) ∧
      (∀ t : Γ(F, U), F.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
        ∃ n : ℕ, f ^ n • t = 0) := by sorry
