-- Prove2me | Theorems.Thm_GlobalTheory_T_hodge_projection_from_lattice
-- name    : GlobalTheory.T.hodge_projection_from_lattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:36.413805+00:00
-- url     : https://prove2.me/theorems/3f5b2485-945e-5c70-85f1-e59a55cbaff6
-- title:
--   T: hodge projection from lattice
-- statement:
--   The T construction uses the hodge projection from lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionFromLatticeStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeProjectionFromLatticeStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionFromLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionFromLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hodge_projection_from_lattice : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by sorry
