-- Prove2me | Theorems.Thm_MohP3_FormalLocal_generation
-- name    : MohP3.FormalLocal.generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:30.177827+00:00
-- url     : https://prove2.me/theorems/1edea1fe-cb51-4583-bbc8-cec1ccab5ba5
-- title:
--   Formal Local: generation
-- statement:
--   **The completed generation statement.**  Every formal power series in
--   `x, y, z` is, modulo the curve ideal, a `k[[y]]`-linear combination of the
--   eight explicit generators.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L511-L543
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L511-L543

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.generation (k : Type*) [Field k] [CharZero k] : Generation k := by sorry
