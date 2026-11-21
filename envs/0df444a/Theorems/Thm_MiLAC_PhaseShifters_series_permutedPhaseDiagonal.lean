-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_series_permutedPhaseDiagonal
-- name    : MiLAC.PhaseShifters.series_permutedPhaseDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:26.961009+00:00
-- url     : https://prove2.me/theorems/332963aa-03b1-47c4-957e-97ddd1444595
-- title:
--   Phase Shifters: series permuted Phase Diagonal
-- statement:
--   The series of two permuted diagonal matrices is a permuted diagonal matrix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L68-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L68-L81

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.series_permutedPhaseDiagonal
    {n : ℕ} (φ ψ : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) :
    ∃ χ : Fin n → ℝ, ∃ ρ : Equiv.Perm (Fin n),
      series (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by sorry
