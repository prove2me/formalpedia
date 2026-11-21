-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_implementable_iff_permutedPhaseDiagonal
-- name    : MiLAC.PhaseShifters.implementable_iff_permutedPhaseDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:26.06632+00:00
-- url     : https://prove2.me/theorems/a5c73537-3bea-418e-b6f7-7105065502ac
-- title:
--   Phase Shifters: implementable iff permuted Phase Diagonal
-- statement:
--   A network is implementable if and only if it is a permuted diagonal matrix of phases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L131-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L131-L137

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.implementable_iff_permutedPhaseDiagonal {n : ℕ} {S : Network n} :
    Implementable S ↔
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by sorry
