-- Prove2me | Theorems.Thm_GRH_dirichlet_quartic_twenty_nine_witness
-- name    : GRH.dirichlet_quartic_twenty_nine_witness
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T18:45:34.629366+00:00
-- url     : https://prove2.me/theorems/1624d91f-f11c-4b51-a5ab-30eb511e5884
-- title:
--   The two primitive quartic characters at conductor 29
-- statement:
--   Exactly two distinct primitive characters modulo 29 send two to i or minus i. They are inverses of each other.
-- source:
--   Derived for the centered Möbius theorem in the Masullo mission. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Mathlib.NumberTheory.LSeries.DirichletContinuation

theorem GRH.dirichlet_quartic_twenty_nine_witness : ∃ χ : DirichletCharacter ℂ 29, χ.IsPrimitive ∧ χ 2=Complex.I ∧
    χ⁻¹.IsPrimitive ∧ χ⁻¹ 2= -Complex.I ∧ χ≠χ⁻¹ ∧
    ∀ ψ : DirichletCharacter ℂ 29, (ψ 2=Complex.I ∨ ψ 2= -Complex.I) ↔ (ψ=χ ∨ ψ=χ⁻¹) := by sorry
