-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_finite_sections_pushforward
-- name    : GlobalTheory.QCoh.finite_sections_pushforward
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:01:46.920242+00:00
-- url     : https://prove2.me/theorems/516d243d-6e6a-5056-a0a1-578489efc57f
-- title:
--   QCoh: finite sections pushforward
-- statement:
--   The QCoh construction uses the finite sections pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L141-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L141-L148

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

theorem GlobalTheory.QCoh.finite_sections_pushforward [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)
    [hF : Module.Finite Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)] :
    Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V) := by sorry
