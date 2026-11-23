-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_pull_coboundary
-- name    : GlobalTheory.KuennethOne.pull_coboundary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:08.646205+00:00
-- url     : https://prove2.me/theorems/9be3ac50-e5fd-4e20-824e-89ebe7227af8
-- title:
--   Kuenneth One: pull coboundary
-- statement:
--   The Kuenneth One construction uses the pull coboundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L110-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L110-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.KuennethOne
variable {Z : Scheme.{0}}
variable {I : Type} (V : I → Z.Opens) (φ : ∀ a b, Γ(Z, V a ⊓ V b))
variable {V φ}

theorem GlobalTheory.KuennethOne.pull_coboundary (hV : ⨆ a, V a = ⊤) {T : Scheme.{0}} (f : T ⟶ Z)
    (ρ : ∀ a, Γ(T, f ⁻¹ᵁ V a))
    (hρ : ∀ a b, (f.app (V a ⊓ V b)).hom (φ a b) =
      rs (f.preimage_mono inf_le_left) (ρ a) - rs (f.preimage_mono inf_le_right) (ρ b))
    {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (N : J → T.Opens) (hN : ∀ j, N j ≤ f ⁻¹ᵁ O j) :
    ∃ x : ∀ j, Γ(T, N j), ∀ j k (P : Z.Opens) (hj : P ≤ O j) (hk : P ≤ O k) (c : Γ(Z, P)),
      IsDiff V (ψ j) (ψ k) hj hk c → ∀ (M : T.Opens) (hMj : M ≤ N j) (hMk : M ≤ N k)
        (hM : M ≤ f ⁻¹ᵁ P), (f.appLE P M hM).hom c = rs hMj (x j) - rs hMk (x k) := by sorry
