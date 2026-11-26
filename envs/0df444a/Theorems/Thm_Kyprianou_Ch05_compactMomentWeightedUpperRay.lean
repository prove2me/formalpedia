-- Prove2me | Theorems.Thm_Kyprianou_Ch05_compactMomentWeightedUpperRay
-- name    : Kyprianou.Ch05.compactMomentWeightedUpperRay
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:50:06.126517+00:00
-- url     : https://prove2.me/theorems/7b9f0147-23e1-4612-b38e-81cbef07fd81
-- title:
--   Moment convergence on the compact unit interval gives bounded weighted upper-ray mass convergence
-- statement:
--   Moment convergence on the compact unit interval gives bounded weighted upper-ray mass convergence
-- source:
--   Kyprianou (2006), Theorem 5.13, compact moment proof of the Tauberian direction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.compactMomentWeightedUpperRay
    {I : Type} (l : Filter I) (N : I → Measure Real) (R : Measure Real)
    (hfin : ∀ i, N i univ ≠ ⊤) (hfinR : R univ ≠ ⊤)
    (hs : ∀ i, ∀ᵐ z ∂(N i), z ∈ Icc (0 : Real) 1)
    (hsR : ∀ᵐ z ∂ R, z ∈ Icc (0 : Real) 1)
    (hi : ∀ (i : I) (n : Nat), Integrable (fun z : Real => z^n) (N i))
    (hiR : ∀ n : Nat, Integrable (fun z : Real => z^n) R)
    (hmom : ∀ n : Nat, Tendsto (fun i => ∫ z : Real, z^n ∂(N i)) l
      (nhds (∫ z : Real, z^n ∂ R)))
    (c : Real) (hc : 0 < c) (hAtom : R {c} = 0) :
    Tendsto (fun i => ((N i).withDensity
      (fun z : Real => ENNReal.ofReal ((max z c)⁻¹)) (Ici c)).toReal) l
      (nhds (((R.withDensity
        (fun z : Real => ENNReal.ofReal ((max z c)⁻¹))) (Ici c)).toReal)) := by sorry
