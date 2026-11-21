-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_parallel_permutedPhaseDiagonal
-- name    : MiLAC.PhaseShifters.parallel_permutedPhaseDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:26.917499+00:00
-- url     : https://prove2.me/theorems/f243cf61-c1ec-49e1-8735-8f91f22eff03
-- title:
--   Phase Shifters: parallel permuted Phase Diagonal
-- statement:
--   The parallel of two permuted diagonal matrices is a permuted diagonal matrix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L84-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L84-L95

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.parallel_permutedPhaseDiagonal
    {n m : ℕ} (φ : Fin n → ℝ) (ψ : Fin m → ℝ)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    ∃ χ : Fin (n + m) → ℝ, ∃ ρ : Equiv.Perm (Fin (n + m)),
      parallel (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by sorry
