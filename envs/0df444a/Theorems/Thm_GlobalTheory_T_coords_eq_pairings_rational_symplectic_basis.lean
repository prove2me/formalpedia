-- Prove2me | Theorems.Thm_GlobalTheory_T_coords_eq_pairings_rational_symplectic_basis
-- name    : GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:53.349301+00:00
-- url     : https://prove2.me/theorems/ac96a8d7-9765-4155-aca1-abdf1507fa59
-- title:
--   T: coords eq pairings rational symplectic basis
-- statement:
--   The T construction uses the coords eq pairings rational symplectic basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoordsEqPairingsRationalSymplecticBasisStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CoordsEqPairingsRationalSymplecticBasisStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoordsEqPairingsRationalSymplecticBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoordsEqPairingsRationalSymplecticBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) → (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by sorry
