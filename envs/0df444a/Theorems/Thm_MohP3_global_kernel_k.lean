-- Prove2me | Theorems.Thm_MohP3_global_kernel_k
-- name    : MohP3.global_kernel_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:59.678078+00:00
-- url     : https://prove2.me/theorems/4389d192-9801-589f-b908-3eb477a5bdd9
-- title:
--   Moh P3: global kernel k
-- statement:
--   **The global kernel computation over an arbitrary characteristic-zero
--   field**: the kernel of the parametrization is exactly the curve ideal.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L262-L279
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L262-L279

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.global_kernel_k : RingHom.ker (rho_k k) = Ppoly k := by sorry
