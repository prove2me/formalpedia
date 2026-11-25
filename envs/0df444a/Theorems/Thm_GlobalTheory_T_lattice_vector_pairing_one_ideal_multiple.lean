-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_vector_pairing_one_ideal_multiple
-- name    : GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:29.927916+00:00
-- url     : https://prove2.me/theorems/97f35193-0a78-405a-b94d-3e3c9153dee0
-- title:
--   T: lattice vector pairing one ideal multiple
-- statement:
--   The T construction uses the lattice vector pairing one ideal multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeVectorPairingOneIdealMultipleStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeVectorPairingOneIdealMultipleStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeVectorPairingOneIdealMultiple
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeVectorPairingOneIdealMultipleStatement
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

theorem GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) →
    (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ {v : V} (K : FractionalIdeal (𝓞 F)⁰ F), K ≠ 0 →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by sorry
