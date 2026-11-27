-- Prove2me | Theorems.Thm_MohP3_FormalLocal_indepS
-- name    : MohP3.FormalLocal.indepS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:59.825129+00:00
-- url     : https://prove2.me/theorems/acf81599-8b23-4ec0-8ab7-e04305509739
-- title:
--   Formal Local: indep S
-- statement:
--   The formal-local analogue of `MohP3.indep`: the eight power series
--   `psi (hh i)` are linearly independent over `k[[t^8]]`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L240-L283
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L240-L283

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.indepS (p : Fin 8 → PowerSeries k) (hs : ∑ i, exp8 k (p i) * vvS k i = 0) :
    ∀ i, p i = 0 := by sorry
