-- Prove2me | Theorems.Thm_MiLAC_parallel_natAdd_natAdd
-- name    : MiLAC.parallel_natAdd_natAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:05.988512+00:00
-- url     : https://prove2.me/theorems/097cf2d9-a778-489f-9b27-852d50615ec5
-- title:
--   Mi LAC: parallel nat Add nat Add
-- statement:
--   The lower-right block of a parallel is the second network.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L83-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L83-L85

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.parallel_natAdd_natAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin m) : parallel A B (Fin.natAdd n i) (Fin.natAdd n j) = B i j := by sorry
