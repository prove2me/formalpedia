-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_implementable_if_permutedPhaseDiagonal
-- name    : MiLAC.PhaseShifters.implementable_if_permutedPhaseDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:23.28119+00:00
-- url     : https://prove2.me/theorems/ed2b966f-e1f5-4bdd-8114-e4209e866775
-- title:
--   Phase Shifters: implementable if permuted Phase Diagonal
-- statement:
--   A permuted diagonal matrix of phases is implementable (sufficient condition).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L57-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L57-L63

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.implementable_if_permutedPhaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Implementable (permutedPhaseDiagonal φ σ) := by sorry
