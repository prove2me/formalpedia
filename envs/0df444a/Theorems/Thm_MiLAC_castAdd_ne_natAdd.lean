-- Prove2me | Theorems.Thm_MiLAC_castAdd_ne_natAdd
-- name    : MiLAC.castAdd_ne_natAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:02.390572+00:00
-- url     : https://prove2.me/theorems/49232d97-2d5b-4061-bf3f-5ad7534e4bb2
-- title:
--   Mi LAC: cast Add ne nat Add
-- statement:
--   The first and second blocks of a parallel network have disjoint ports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L58-L60
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L58-L60

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by sorry
