-- Prove2me | Theorems.Thm_MinModulus_elementaryAbelianTwoGroups_optimal
-- name    : MinModulus.elementaryAbelianTwoGroups_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:39:54.965895+00:00
-- url     : https://prove2.me/theorems/b857c167-28eb-4ce7-aa43-b20f55791773
-- title:
--   Min Modulus: elementary Abelian Two Groups optimal
-- statement:
--   The Min Modulus construction uses the elementary Abelian Two Groups optimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/ElemAbelian2.lean#L163-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/ElemAbelian2.lean#L163-L219

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.GroupAction.Ring
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_ElemAbelian2
set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open scoped BigOperators
open Module

theorem MinModulus.elementaryAbelianTwoGroups_optimal
    {n k : ℕ} (g : Fin n → (Fin k → ZMod 2))
    (huniq : UniqueMultisetSums g) : n - 1 ≤ k := by sorry
