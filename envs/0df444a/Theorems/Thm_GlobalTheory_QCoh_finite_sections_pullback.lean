-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_finite_sections_pullback
-- name    : GlobalTheory.QCoh.finite_sections_pullback
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:32.43084+00:00
-- url     : https://prove2.me/theorems/674ea98f-7ecb-5258-be66-60f134d8aefd
-- title:
--   QCoh: finite sections pullback
-- statement:
--   The QCoh construction uses the finite sections pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L494-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L494-L500

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) {U : X.Opens} {V : Y.Opens}
variable [G.IsQuasicoherent]

theorem GlobalTheory.QCoh.finite_sections_pullback (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    [Module.Finite Γ(Y, V) Γ(G, V)] :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U) := by sorry
