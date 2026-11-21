-- Prove2me | Theorems.Thm_MiLAC_natAdd_ne_castAdd
-- name    : MiLAC.natAdd_ne_castAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:36:06.184199+00:00
-- url     : https://prove2.me/theorems/e48b84b9-6212-4222-aefe-6c94c7d047be
-- title:
--   Mi LAC: nat Add ne cast Add
-- statement:
--   Disjointness of parallel ports with the two blocks interchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L63-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/Basic.lean#L63-L65

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
open MiLAC

theorem MiLAC.natAdd_ne_castAdd {n m : ℕ} (i : Fin m) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd m j := by sorry
