-- Prove2me | Theorems.Thm_GlobalTheory_exists_fractionalIdeal_smul_mem_lattice_of_alternating
-- name    : GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:27.270824+00:00
-- url     : https://prove2.me/theorems/cf5694f7-9410-4f31-b321-c8ce96c7d9c2
-- title:
--   Global Theory: exists fractional Ideal smul mem lattice of alternating
-- statement:
--   The Global Theory construction uses the exists fractional Ideal smul mem lattice of alternating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealDualVectorIntegral.lean#L7-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealDualVectorIntegral.lean#L7-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealDualVectorIntegral
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
open GlobalTheory

theorem GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating
    {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    (L : Set V) (h0 : (0 : V) ∈ L) (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hBJ : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by sorry
