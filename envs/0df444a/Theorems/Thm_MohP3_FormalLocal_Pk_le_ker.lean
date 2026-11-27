-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Pk_le_ker
-- name    : MohP3.FormalLocal.Pk_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:50.538846+00:00
-- url     : https://prove2.me/theorems/31120917-2404-48ec-a8ef-59b85720ea67
-- title:
--   Formal Local: Pk le ker
-- statement:
--   The Formal Local construction uses the Pk le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L141-L149
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L141-L149

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
omit [CharZero k]

theorem MohP3.FormalLocal.Pk_le_ker : Pk k ≤ RingHom.ker (psi k) := by sorry
