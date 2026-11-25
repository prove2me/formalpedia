-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_quasicoherent_push_pull
-- name    : GlobalTheory.QCoh.quasicoherent_push_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:45.306938+00:00
-- url     : https://prove2.me/theorems/01f7e205-655e-5312-a72a-dbba48ebdc96
-- title:
--   QCoh: quasicoherent push pull
-- statement:
--   The QCoh construction uses the quasicoherent push pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L625-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L625-L652

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

theorem GlobalTheory.QCoh.quasicoherent_push_pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (QuasiCompact f → QuasiSeparated f → ∀ F : X.Modules, F.IsQuasicoherent →
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent) ∧
    (IsFinite f ∨ IsClosedImmersion f → ∀ F : X.Modules, F.IsQuasicoherent →
      (∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)) →
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent ∧
        ∀ V : Y.Opens, IsAffineOpen V →
          Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V)) ∧
    (IsAffineHom f → ∀ S : ShortComplex X.Modules, S.ShortExact → S.X₂.IsQuasicoherent →
      S.X₃.IsQuasicoherent → (S.map (Scheme.Modules.pushforward f)).ShortExact) ∧
    (∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback f).obj G).IsQuasicoherent ∧
      ∀ (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
        letI := appLEAlgebra f e
        letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
        haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
        IsBaseChange Γ(X, U) (pullbackSections f G e)) ∧
    (∀ S : ShortComplex Y.Modules, S.Exact → Epi S.g →
      (S.map (Scheme.Modules.pullback f)).Exact ∧ Epi (S.map (Scheme.Modules.pullback f)).g) ∧
    (Flat f → ∀ S : ShortComplex Y.Modules, S.ShortExact → S.X₁.IsQuasicoherent →
      S.X₂.IsQuasicoherent → (S.map (Scheme.Modules.pullback f)).ShortExact) := by sorry
