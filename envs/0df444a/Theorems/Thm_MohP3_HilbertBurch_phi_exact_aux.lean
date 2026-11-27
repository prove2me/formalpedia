-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_phi_exact_aux
-- name    : MohP3.HilbertBurch.phi_exact_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:59.330811+00:00
-- url     : https://prove2.me/theorems/8c4c1b1e-aee1-494c-bfd1-3c9f1825f6e6
-- title:
--   Hilbert Burch: phi exact aux
-- statement:
--   **Hilbert–Burch presentation, first half.** Over `S = k[x,y,z]` the manuscript's
--   matrix `Φ : S^3 → S^4` is injective, and its image is exactly the module of
--   relations among `f1, f2, f3, f4`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L371-L380
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L371-L380

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.HilbertBurch.phi_exact_aux :
    Function.Injective (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) ∧
      LinearMap.range (Matrix.mulVecLin (phi (X 0) (X 1) (X 2) : Matrix (Fin 4) (Fin 3)
        (MvPolynomial (Fin 3) k))) = LinearMap.ker (rowMap (fvec (X 0) (X 1) (X 2))) := by sorry
