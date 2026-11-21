-- Prove2me | Theorems.Thm_MiLAC_PhaseShifters_permutedPhaseDiagonal_apply
-- name    : MiLAC.PhaseShifters.permutedPhaseDiagonal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:22.949284+00:00
-- url     : https://prove2.me/theorems/ff19425f-819f-40b4-819b-9fc9f50ee875
-- title:
--   Phase Shifters: permuted Phase Diagonal apply
-- statement:
--   An entry of a permuted phase diagonal has at most one nonzero value per row.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L46-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean#L46-L52

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters

theorem MiLAC.PhaseShifters.permutedPhaseDiagonal_apply {n : ℕ} (φ : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutedPhaseDiagonal φ σ i j =
      if σ i = j then Complex.exp (φ (σ i) * Complex.I) else 0 := by sorry
