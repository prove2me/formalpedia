-- Prove2me | Theorems.Thm_MiLAC_parallel_natAdd_castAdd
-- name    : MiLAC.parallel_natAdd_castAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:07.410187+00:00
-- url     : https://prove2.me/theorems/be40923d-6121-4807-b404-f8e7578f8c2f
-- title:
--   Mi LAC: parallel nat Add cast Add
-- statement:
--   The lower-left block of a parallel is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L78-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L78-L80

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.parallel_natAdd_castAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i : Fin m) (j : Fin n) : parallel A B (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by sorry
