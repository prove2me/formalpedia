-- Prove2me | Theorems.Thm_LatinQuarter_corner_forcing_step
-- name    : LatinQuarter.corner_forcing_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:31.484172+00:00
-- url     : https://prove2.me/theorems/3d2e3fd0-11d3-4e4a-b705-3cc6f52b5af1
-- title:
--   Latin Quarter: corner forcing step
-- statement:
--   Every non-corner cell is forced by the cells preceding it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L58-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L58-L111

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.corner_forcing_step {n : ℕ} (hn : 0 < n) (M : Square n)
    (hM : IsLatin M) (ha : Agrees (cornerSet n) (cyclic n) M)
    (r c : Fin n)
    (hprev : ∀ i j, fillingOrder i j < fillingOrder r c → M i j = cyclic n i j) :
    M r c = cyclic n r c := by sorry
