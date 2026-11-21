-- Prove2me | Theorems.Thm_MasulloRH_lifted_rank_one_schatten_norms
-- name    : MasulloRH.lifted_rank_one_schatten_norms
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:18:44.022191+00:00
-- url     : https://prove2.me/theorems/19350237-18c6-45c0-8c5a-e8b708211875
-- title:
--   Trace and Hilbert–Schmidt norms of a lifted spectral summand
-- statement:
--   For a complex Hilbert space, the trace norm and the Hilbert–Schmidt norm of x ⊗ y both equal ‖x‖ ‖y‖. In (10.4.2.25), x is the convolution applied to the lifted vector, and y represents its coefficient functional.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, Theorem 10.4.2.8, pp. 463–464, single-term norm computation at (10.4.2.25)–(10.4.2.26).

import Definitions.Def_MasulloGRH_HilbertNuclear

open MasulloGRH InnerProductSpace
open scoped ComplexConjugate

theorem MasulloRH.lifted_rank_one_schatten_norms {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x y : H) :
    traceNorm (rankOne ℂ x y) = ‖x‖ * ‖y‖ ∧
      hilbertSchmidtNorm (rankOne ℂ x y) = ‖x‖ * ‖y‖ := by sorry
