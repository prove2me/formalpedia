-- Prove2me | Theorems.Thm_MiLAC_parallel_castAdd_castAdd
-- name    : MiLAC.parallel_castAdd_castAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:05.740399+00:00
-- url     : https://prove2.me/theorems/a44cada7-22f6-481f-8fe2-892fc16d7053
-- title:
--   Mi LAC: parallel cast Add cast Add
-- statement:
--   The upper-left block of a parallel is the first network.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L68-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L68-L70

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.parallel_castAdd_castAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin n) : parallel A B (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by sorry
