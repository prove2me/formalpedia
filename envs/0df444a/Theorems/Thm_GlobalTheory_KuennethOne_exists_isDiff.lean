-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_exists_isDiff
-- name    : GlobalTheory.KuennethOne.exists_isDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:56.111183+00:00
-- url     : https://prove2.me/theorems/8fa6cb27-1e70-47c3-9630-ef40f68e795f
-- title:
--   Kuenneth One: exists is Diff
-- statement:
--   The Kuenneth One construction uses the exists is Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitsOfIsAffineOpen.lean#L66-L82

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

theorem GlobalTheory.KuennethOne.exists_isDiff (hV : ⨆ a, V a = ⊤) {O O' P : Z.Opens} {ψ : ∀ a, Γ(Z, O ⊓ V a)}
    {ψ' : ∀ a, Γ(Z, O' ⊓ V a)} (h : Splits V φ O ψ) (h' : Splits V φ O' ψ')
    (hO : P ≤ O) (hO' : P ≤ O') : ∃ c : Γ(Z, P), IsDiff V ψ ψ' hO hO' c := by sorry
