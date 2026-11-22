-- Prove2me | Theorems.Thm_Nock_NPR_dyckBits_cell
-- name    : Nock.NPR.dyckBits_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:53.586413+00:00
-- url     : https://prove2.me/theorems/3abebe5e-6183-40dd-b29e-2760d6e937b7
-- title:
--   NPR: dyck Bits cell
-- statement:
--   Dyck word under `cell`: `w = 0 · w_L · 1 · w_R` (the grammar of `Dyck.encode`,
--       main.tex:337), cast to field bits (`false ↦ 0`, `true ↦ 1`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L238-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NPR.lean#L238-L243

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]

theorem Nock.NPR.dyckBits_cell (l r : Noun) :
    dyckBits (K := K) (Noun.cell l r)
      = (0 : K) :: (dyckBits l ++ (1 : K) :: dyckBits r) := by sorry
