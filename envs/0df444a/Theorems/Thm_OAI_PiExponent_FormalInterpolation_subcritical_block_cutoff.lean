-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_subcritical_block_cutoff
-- name    : OAI.PiExponent.FormalInterpolation.subcritical_block_cutoff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:09:01.422118+00:00
-- url     : https://prove2.me/theorems/8e22c9ba-9e41-4fd1-8384-12618f5f1dc5
-- title:
--   Subcritical generator degree gives an eventual block cutoff
-- statement:
--   For R > 0 and D < sR, sufficiently large n admits a block index k with ks < n ≤ (k + 1)s and C + k * max(D, 0) ≤ nR.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.subcritical_block_cutoff
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : D < (s : Real) * R)
    (C : Real) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∃ k : Nat, k * s < n ∧ n ≤ (k + 1) * s ∧
        C + (k : Real) * max D 0 ≤ (n : Real) * R := by sorry
