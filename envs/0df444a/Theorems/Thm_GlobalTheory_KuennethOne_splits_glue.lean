-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_splits_glue
-- name    : GlobalTheory.KuennethOne.splits_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:16.541623+00:00
-- url     : https://prove2.me/theorems/1df3e6ff-7158-4ad4-9738-8f87ac418218
-- title:
--   Kuenneth One: splits glue
-- statement:
--   The Kuenneth One construction uses the splits glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L84-L108

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

theorem GlobalTheory.KuennethOne.splits_glue {J : Type} (O : J → Z.Opens) (ψ : ∀ j a, Γ(Z, O j ⊓ V a))
    (h : ∀ j, Splits V φ (O j) (ψ j)) (g : ∀ j, Γ(Z, O j))
    (hg : ∀ j k a (M : Z.Opens) (hj : M ≤ O j) (hk : M ≤ O k) (ha : M ≤ V a),
      rs (le_inf hj ha) (ψ j a) - rs (le_inf hk ha) (ψ k a) = rs hj (g j) - rs hk (g k))
    (O₀ : Z.Opens) (hc : O₀ ≤ iSup O) : ∃ χ, Splits V φ O₀ χ := by sorry
