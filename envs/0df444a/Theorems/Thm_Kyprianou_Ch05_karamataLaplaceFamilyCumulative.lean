-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataLaplaceFamilyCumulative
-- name    : Kyprianou.Ch05.karamataLaplaceFamilyCumulative
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:42:40.160395+00:00
-- url     : https://prove2.me/theorems/d9165042-12be-55f8-8d09-af5e6ced96ba
-- title:
--   Laplace convergence to a nonnegative reference measure gives convergence of cumulative mass at a continuity point
-- statement:
--   Laplace convergence to a nonnegative reference measure gives convergence of cumulative mass at a continuity point
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17. Laplace–Stieltjes Tauberian implication.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataLaplaceFamilyCumulative
    {I : Type} (l : Filter I) (M : I → Measure Real) (R : Measure Real)
    (hs : ∀ i, M i (Iio 0) = 0) (hsR : R (Iio 0) = 0)
    (hfin : ∀ i (t : Real), 0 < t → positiveLaplace (M i) t ≠ ⊤)
    (hfinR : ∀ t : Real, 0 < t → positiveLaplace R t ≠ ⊤)
    (hconv : ∀ n : Nat, Tendsto
      (fun i => (positiveLaplace (M i) ((n : Real)+1)).toReal) l
      (nhds (positiveLaplace R ((n : Real)+1)).toReal))
    (hAtom : R {1} = 0) :
    Tendsto (fun i => (M i (Icc 0 1)).toReal) l (nhds (R (Icc 0 1)).toReal) := by sorry
