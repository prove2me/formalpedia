-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_form_ideal_generates_dual_vector
-- name    : GlobalTheory.T.lattice_form_ideal_generates_dual_vector
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:29.890185+00:00
-- url     : https://prove2.me/theorems/a5bd8dae-c0d5-5aba-b5b7-8734672f111a
-- title:
--   T: lattice form ideal generates dual vector
-- statement:
--   The T construction uses the lattice form ideal generates dual vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealGeneratesDualVectorStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealGeneratesDualVectorStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealGeneratesDualVector
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealGeneratesDualVectorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_form_ideal_generates_dual_vector : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v := by sorry
