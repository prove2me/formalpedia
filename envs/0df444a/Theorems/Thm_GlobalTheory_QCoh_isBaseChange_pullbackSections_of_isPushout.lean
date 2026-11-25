-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_pullbackSections_of_isPushout
-- name    : GlobalTheory.QCoh.isBaseChange_pullbackSections_of_isPushout
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:31.192672+00:00
-- url     : https://prove2.me/theorems/ef4414f3-846a-441c-8335-c0cef15e0715
-- title:
--   QCoh: is Base Change pullback Sections of is Pushout
-- statement:
--   The QCoh construction uses the is Base Change pullback Sections of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L466-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L466-L492

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

theorem GlobalTheory.QCoh.isBaseChange_pullbackSections_of_isPushout (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra A Γ(Y, V)] [Algebra B Γ(X, U)] [Algebra A Γ(X, U)] [Algebra Γ(Y, V) Γ(X, U)]
    [IsScalarTower A B Γ(X, U)] [IsScalarTower A Γ(Y, V) Γ(X, U)]
    [Algebra.IsPushout A B Γ(Y, V) Γ(X, U)]
    (halg : ∀ r, algebraMap Γ(Y, V) Γ(X, U) r = f.appLE V U e r)
    [Module A Γ(G, V)] [IsScalarTower A Γ(Y, V) Γ(G, V)]
    [Module A Γ((Scheme.Modules.pullback f).obj G, U)]
    [Module B Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower A B Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower B Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U)]
    (l : Γ(G, V) →ₗ[A] Γ((Scheme.Modules.pullback f).obj G, U))
    (hl : ∀ s, l s = pullbackSections f G e s) : IsBaseChange B l := by sorry
