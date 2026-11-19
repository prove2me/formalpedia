-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finsetVectorLawsOfFinArrayLaws
-- name    : Kyprianou.Ch01.finsetVectorLawsOfFinArrayLaws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:18:32.133212+00:00
-- url     : https://prove2.me/theorems/5873e999-9e10-4042-acd5-8b461566ceee
-- title:
--   Finite-set joint laws from Fin n joint laws for integer paths
-- statement:
--   Any finite set of time coordinates can be enumerated by Fin n, so equality of every Fin n vector pushforward law implies equality of pushforward laws indexed by arbitrary finite subsets. This is the exact combinatorial bridge needed for finite-dimensional path-measure uniqueness.
-- source:
--   Kyprianou 2006 Chapter 1 Lamperti forward path-law, reduction helper; Finset.equivFin and measurable coordinate projections.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Data.Fintype.EquivFin
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finsetVectorLawsOfFinArrayLaws
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (F : Ω → (ι → ℤ)) (G : Ω' → (ι → ℤ))
    (hF : Measurable F) (hG : Measurable G)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ι,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    ∀ J : Finset ι,
      P.map (fun ω => fun j : J => F ω j) =
        Q.map (fun ω => fun j : J => G ω j) := by
  sorry
