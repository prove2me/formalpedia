-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_uniform_finite_adjoin_module_generators
-- name    : OAI.PiExponent.FormalInterpolation.uniform_finite_adjoin_module_generators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:04:41.903442+00:00
-- url     : https://prove2.me/theorems/98386071-9088-4cf9-89ac-1aa314334c7a
-- title:
--   Finite module generators with coefficients in the adjoin
-- statement:
--   Finite generation as a module over the adjoined subalgebra gives one fixed finite family of ambient generators, with every ambient polynomial expressible as a linear combination whose coefficients lie in the adjoin.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.uniform_finite_adjoin_module_generators
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
      ∀ q : MvPolynomial (Fin d) Complex,
        ∃ c : Fin t → Algebra.adjoin Complex (Set.range g),
          q = ∑ i : Fin t, (c i : MvPolynomial (Fin d) Complex) * b i := by sorry
