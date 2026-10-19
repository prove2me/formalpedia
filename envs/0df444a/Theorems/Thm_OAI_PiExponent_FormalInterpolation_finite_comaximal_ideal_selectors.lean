-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_comaximal_ideal_selectors
-- name    : OAI.PiExponent.FormalInterpolation.finite_comaximal_ideal_selectors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:36:12.587753+00:00
-- url     : https://prove2.me/theorems/c4bf4dd2-68cd-4014-b6ff-09e459c21d86
-- title:
--   Selectors for a finite family of pairwise comaximal ideals
-- statement:
--   For a finite family of pairwise comaximal ideals in a commutative ring, construct elements whose residue is one at their selected ideal and zero at every other ideal. Prove this by finite CRT (or induction on the index set). The empty family case is vacuous and the singleton case uses the unit element.

import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.finite_comaximal_ideal_selectors
    {R : Type} [CommRing R] {K : Nat} (I : Fin K → Ideal R)
    (hI : ∀ j k : Fin K, j ≠ k → I j ⊔ I k = ⊤) :
    ∃ E : Fin K → R, ∀ j k : Fin K,
      E k - (if j = k then 1 else 0) ∈ I j := by sorry
