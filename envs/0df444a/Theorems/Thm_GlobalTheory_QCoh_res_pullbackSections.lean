-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_res_pullbackSections
-- name    : GlobalTheory.QCoh.res_pullbackSections
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:52.483149+00:00
-- url     : https://prove2.me/theorems/0abf974f-7027-5860-958a-7a93ed6070b5
-- title:
--   QCoh: res pullback Sections
-- statement:
--   The QCoh construction uses the res pullback Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L212-L215

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
variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) {U U' : X.Opens} {V V' : Y.Opens}

theorem GlobalTheory.QCoh.res_pullbackSections (e : U ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE h).op (pullbackSections f G e s) =
      pullbackSections f G (h.trans e) s := by sorry
