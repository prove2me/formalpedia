-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_form_change_of_basis_lie
-- name    : GlobalTheory.T.hermitian_form_change_of_basis_lie
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:27.354465+00:00
-- url     : https://prove2.me/theorems/b57ff7db-91a3-4177-aca5-dbf1beb15917
-- title:
--   T: hermitian form change of basis lie
-- statement:
--   The T construction uses the hermitian form change of basis lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockBasisChangeEntriesStatement.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockBasisChangeEntriesStatement.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntries
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntriesStatement
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

theorem GlobalTheory.T.hermitian_form_change_of_basis_lie : ∀ {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ) (J : Matrix (Fin n) (Fin n') ℂ),
    Hᴴ = H → H'ᴴ = H' → IsUnit H.det → IsUnit H'.det → Jᴴ * H * J = H' →
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by sorry
