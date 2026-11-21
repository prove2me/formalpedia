-- Prove2me | Theorems.Thm_MiLAC_parallel_castAdd_natAdd
-- name    : MiLAC.parallel_castAdd_natAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:08.198579+00:00
-- url     : https://prove2.me/theorems/fe1a9f42-50c6-4adb-a0c7-68c60f78ba20
-- title:
--   Mi LAC: parallel cast Add nat Add
-- statement:
--   The upper-right block of a parallel is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L73-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L73-L75

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.parallel_castAdd_natAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i : Fin n) (j : Fin m) : parallel A B (Fin.castAdd m i) (Fin.natAdd n j) = 0 := by sorry
