-- Prove2me | Theorems.Thm_GRH_twisted_mobius_square_root_on_conductor_ranges
-- name    : GRH.twisted_mobius_square_root_on_conductor_ranges
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:54:54.378664+00:00
-- url     : https://prove2.me/theorems/2ef54a81-b70d-48ed-853a-f45978137190
-- title:
--   Simultaneous square-root Möbius cancellation through the conductor for at least seven ninths of Dirichlet characters
-- statement:
--   For every modulus q≥1 there is one set G of at least 7φ(q)/9 Dirichlet characters such that the following holds simultaneously for all χ∈G and all integers N≥1. For Sχ(N)=Σ_{n≤N}χ(n)μ(n), we have |Sχ(N)|²≤18N(⌊log₂N⌋+2)⁴(1+2N/q). Consequently the bound is at most 54N(⌊log₂N⌋+2)⁴ for N≤q and at most 54N^(5/3)(⌊log₂N⌋+2)⁴ for N≤q³. At prime level all members except possibly the principal character are primitive, with at least 7φ(q)/9−1 such good primitive characters. This is a conductor-uniform majority estimate across all prefixes. It leaves open the square-root exponent along N→∞ for each individual character.
-- source:
--   Partial arithmetic estimate toward the open Prove2Me leaf GRH.sharp_mobius_character_power_bound_below_record, https://prove2.me/theorems/c539a029-f395-4317-ae41-5b59dc0aca19 . The proof specializes finite Dirichlet-character orthogonality and the classical Rademacher–Menšov dyadic maximal argument. For the classical maximal method see F. Móricz, Acta Scientiarum Mathematicarum 40, 143–156, Lemma 1, https://acta.bibl.u-szeged.hu/14667/1/math_040_fasc_001_002_143-156.pdf . All analytic and combinatorial estimates used here are included in the Lean submission.

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

open Finset Complex
open scoped Classical

theorem GRH.twisted_mobius_square_root_on_conductor_ranges (q : ℕ) [NeZero q] :
    let S (χ : DirichletCharacter ℂ q) (N : ℕ) :=
      ∑ k ∈ range N, χ (k+1:ℕ) * (ArithmeticFunction.moebius (k+1):ℂ)
    let H (N : ℕ) := ((Nat.log 2 N : ℝ)+2)^4
    ∃ G : Finset (DirichletCharacter ℂ q), 7*q.totient ≤ 9*G.card ∧
      7*q.totient ≤ 9*(G.erase 1).card+9 ∧
      (q.Prime → ∀ χ ∈ G.erase 1, χ.IsPrimitive) ∧
      ∀ χ ∈ G, ∀ N : ℕ, 0<N →
        ‖S χ N‖^2 ≤ 18*N*H N*(1+2*(N:ℝ)/q) ∧
        (N≤q → ‖S χ N‖^2 ≤ 54*N*H N) ∧
        (N≤q^3 → ‖S χ N‖^2 ≤ 54*(N:ℝ)^(5/3:ℝ)*H N) := by sorry
