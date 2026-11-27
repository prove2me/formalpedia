-- Prove2me | Theorems.Thm_GRH_dirichlet_nonvanishing_of_integrable_one_class_prime_deficit
-- name    : GRH.dirichlet_nonvanishing_of_integrable_one_class_prime_deficit
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:21:48.453128+00:00
-- url     : https://prove2.me/theorems/31625fa4-5d95-4795-a49e-a4d3a364de39
-- title:
--   An integrated prime shortfall excludes zeros of every Dirichlet character at one modulus
-- statement:
--   For 0<θ<1 and fixed q>0, finite Mellin integral of the positive prime deficit against x^(−θ−1) excludes every Dirichlet L-function zero in Re(s)>θ, with the principal pole at 1 excluded.
-- source:
--   The exact Möbius target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 . Its previously verified one-class reduction is https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800 . The Mellin differentiation helpers adapt the public Apache-2.0 source at https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7 . Attribution and license are included in the Lean source.

import Definitions.Def_GRH_PrimeDeficitMean

open MeasureTheory Set Filter Topology ArithmeticFunction GRH.PrimeDeficitMean GRH.SplitPrimeLower GRH.OneSidedMoebius GRH.FactorialMoebius

theorem GRH.dirichlet_nonvanishing_of_integrable_one_class_prime_deficit (q : ℕ) [NeZero q] (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1)
    (h : IntegrableOn (fun x : ℝ => deficit q x*x^(-θ-1)) (Ioi 1)) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ<s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by sorry
