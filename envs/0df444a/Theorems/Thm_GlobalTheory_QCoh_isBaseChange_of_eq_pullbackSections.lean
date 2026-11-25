-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_of_eq_pullbackSections
-- name    : GlobalTheory.QCoh.isBaseChange_of_eq_pullbackSections
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:01:51.248199+00:00
-- url     : https://prove2.me/theorems/98959d2e-6e6b-5803-884f-ca77db1712c8
-- title:
--   QCoh: is Base Change of eq pullback Sections
-- statement:
--   The QCoh construction uses the is Base Change of eq pullback Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L452-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L452-L464

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

theorem GlobalTheory.QCoh.isBaseChange_of_eq_pullbackSections (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) [alg : Algebra Γ(Y, V) Γ(X, U)]
    [mod : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U)]
    (halg : ∀ r, algebraMap Γ(Y, V) Γ(X, U) r = f.appLE V U e r)
    (l : Γ(G, V) →ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj G, U))
    (hl : ∀ s, l s = pullbackSections f G e s) : IsBaseChange Γ(X, U) l := by sorry
