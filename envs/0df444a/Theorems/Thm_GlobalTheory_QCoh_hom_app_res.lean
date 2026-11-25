-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_hom_app_res
-- name    : GlobalTheory.QCoh.hom_app_res
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:43.468368+00:00
-- url     : https://prove2.me/theorems/3218a7ae-3c16-58aa-8488-0525ff173e47
-- title:
--   QCoh: hom app res
-- statement:
--   The QCoh construction uses the hom app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L156-L158

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
variable {X Y : Scheme.{u}}

theorem GlobalTheory.QCoh.hom_app_res {F F' : X.Modules} (φ : F ⟶ F') {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = F'.presheaf.map (homOfLE h).op (φ.app U s) := by sorry
