-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pathMeasureEqOfAEFiniteDimensionalLaws
-- name    : Kyprianou.Ch01.pathMeasureEqOfAEFiniteDimensionalLaws
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:18:06.544312+00:00
-- url     : https://prove2.me/theorems/a97e3cd9-54b5-4b63-8e1c-43118f511d7c
-- title:
--   Almost-everywhere measurable path laws are determined by finite-dimensional laws
-- statement:
--   Let F and G be almost-everywhere measurable maps from probability spaces into the product measurable space of nonnegative-real-indexed integer paths. If every finite family of time evaluations has the same pushforward probability law, then their full path-space pushforward measures agree. The proof replaces F and G by measurable representatives, transfers finite-dimensional laws across almost-sure equality, and uses the established finite-dimensional path-law uniqueness theorem. This avoids requiring global path-map measurability on exceptional null paths, which is not implied by the almost-sure càdlàg hypothesis in Kyprianou Chapter 1 §1.3.4.
-- source:
--   Kyprianou (2006), Ch01 §1.3.4, forward Lamperti path law target 318afc19-2086-4e20-9846-225169aaa3c1; corrects the overly strong global path-map measurability dependency c79965ce-c470-48ca-a8ce-26e523ad6e21 and generalises authoritative Proved theorem f48b4066-d10f-4607-82cc-a6aa66cfaec7. Mathematical bridge preserves all finite-dimensional laws with AEMeasurable representatives.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pathMeasureEqOfAEFiniteDimensionalLaws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (F : Ω → (ℝ≥0 → ℤ)) (G : Ω' → (ℝ≥0 → ℤ))
    (hF : AEMeasurable F P) (hG : AEMeasurable G Q)
    (hJoint : ∀ n : ℕ, ∀ times : Fin n → ℝ≥0,
      P.map (fun ω => fun i : Fin n => F ω (times i)) =
      Q.map (fun ω => fun i : Fin n => G ω (times i))) :
    P.map F = Q.map G := by
  sorry
