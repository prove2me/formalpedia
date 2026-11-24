-- Prove2me | Theorems.Thm_GlobalTheory_T_mobiusInversion_affine_finrank_subspaces
-- name    : GlobalTheory.T.mobiusInversion_affine_finrank_subspaces
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:05.511487+00:00
-- url     : https://prove2.me/theorems/c8a22a94-aeeb-4ae0-965b-c2597cc80ac3
-- title:
--   T: mobius Inversion affine finrank subspaces
-- statement:
--   The T construction uses the mobius Inversion affine finrank subspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusInversionAffineFinrankSubspacesStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusInversionAffineFinrankSubspacesStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mobiusInversion_affine_finrank_subspaces : ∀ (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (G : Submodule K U → ℂ) (c₀ c : ℂ), 0 < Module.finrank K U → (∀ A : Submodule K U, ∑ᶠ B : {B : Submodule K U // B ≤ A}, G B.1 = c₀ + c * (Module.finrank K A : ℂ)) → G ⊤ = c * ∏ i ∈ Finset.Ico 1 (Module.finrank K U), (1 - (Nat.card K : ℂ) ^ i) := by sorry
