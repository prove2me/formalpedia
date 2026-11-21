-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_implementable_only_if_permutedPhaseDiagonal
-- name    : MiLAC.PhaseShifters.implementable_only_if_permutedPhaseDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:25.241617+00:00
-- url     : https://prove2.me/theorems/43f607b2-446d-49b0-a2c8-393b142ea025
-- title:
--   Phase Shifters: implementable only if permuted Phase Diagonal
-- statement:
--   An implementable network is a permuted diagonal matrix of phases (necessary condition).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L98-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L98-L126

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.implementable_only_if_permutedPhaseDiagonal {n : ℕ}
    {S : Network n} (hS : Implementable S) :
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by sorry
