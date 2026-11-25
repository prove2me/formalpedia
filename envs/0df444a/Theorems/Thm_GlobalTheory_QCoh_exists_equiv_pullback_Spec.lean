-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exists_equiv_pullback_Spec
-- name    : GlobalTheory.QCoh.exists_equiv_pullback_Spec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:07.425362+00:00
-- url     : https://prove2.me/theorems/15855357-d82d-4edc-b5e3-bb7c22be1497
-- title:
--   QCoh: exists equiv pullback Spec
-- statement:
--   The QCoh construction uses the exists equiv pullback Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L317-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L317-L332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.exists_equiv_pullback_Spec (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI := φ.hom.toAlgebra
    ∃ e : S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤),
      ∀ m, e (1 ⊗ₜ m) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m := by sorry
