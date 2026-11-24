-- Prove2me | Theorems.Thm_GlobalTheory_IwaFlag_smul_mem_of_sd
-- name    : GlobalTheory.IwaFlag.smul_mem_of_sd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:22.322801+00:00
-- url     : https://prove2.me/theorems/724f358c-930b-4f44-99a4-258f69bc51d5
-- title:
--   Iwa Flag: smul mem of sd
-- statement:
--   The Iwa Flag construction uses the smul mem of sd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFlagDualMatrix.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsFlagDualMatrix.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}

theorem GlobalTheory.IwaFlag.smul_mem_of_sd (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hM₁ : ∀ y ∈ M, ε • y = y)
    (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O)) {o : R} (ho : o ∈ O) {y : V} (hy : y ∈ M) : o • y ∈ M := by sorry
