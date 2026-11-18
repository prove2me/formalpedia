-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteLevyNormalizeNoZeroAtom
-- name    : Kyprianou.Ch01.finiteLevyNormalizeNoZeroAtom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:20:57.503192+00:00
-- url     : https://prove2.me/theorems/82859488-7f94-4486-bc2a-7e1d1215ebde
-- title:
--   Normalised nonzero finite Lévy measure retains zero-free jump support
-- statement:
--   For a finite positive measure Λ with strictly positive total mass and zero atom at the origin, its normalised probability measure assigns zero mass to the origin. This constructs a valid genuine compound-Poisson mark law from the nondegenerate finite logarithmic Lévy intensity for Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), compound-Poisson jump distribution normalisation.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteLevyNormalizeNoZeroAtom
    (Λ : Measure ℝ) (hfinite : Λ Set.univ < ⊤)
    (hpositive : 0 < Λ Set.univ) (hzero : Λ {0} = 0) :
    ((FiniteMeasure.normalize (⟨Λ, ⟨hfinite⟩⟩ : FiniteMeasure ℝ) : Measure ℝ) {0}) = 0 := by
  sorry
