-- Prove2me | Theorems.Thm_MiLAC_interconnection_eq_phaseShifter_zero
-- name    : MiLAC.interconnection_eq_phaseShifter_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:09.178989+00:00
-- url     : https://prove2.me/theorems/a17181ae-3728-4ed0-a124-1c5a7439a699
-- title:
--   Mi LAC: interconnection eq phase Shifter zero
-- statement:
--   An interconnection is a phase shifter with zero phase.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L40-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L40-L45

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.interconnection_eq_phaseShifter_zero :
    interconnection = phaseShifter 0 := by sorry
