-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_mem_ideal_power
-- name    : OAI.PiExponent.FormalInterpolation.scaledProduct_mem_ideal_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T18:15:20.525913+00:00
-- url     : https://prove2.me/theorems/114fe44b-ac68-4dfe-b010-f3fdd4f74e56
-- title:
--   Finite products preserve ideal-power membership
-- statement:
--   A finite product of elements of the same ideal power belongs to the ideal power whose exponent is the number of factors times the original exponent. This includes an empty index type and exponent zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.scaledProduct_mem_ideal_power
    {d : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial (Fin d) Complex)) (s : Nat)
    (f : ι → MvPolynomial (Fin d) Complex)
    (hf : ∀ i, f i ∈ I ^ s) :
    (∏ i : ι, f i) ∈ I ^ (Fintype.card ι * s) := by sorry
