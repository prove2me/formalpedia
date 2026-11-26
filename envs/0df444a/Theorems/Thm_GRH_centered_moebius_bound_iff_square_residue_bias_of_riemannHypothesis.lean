-- Prove2me | Theorems.Thm_GRH_centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
-- name    : GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:53:33.073927+00:00
-- url     : https://prove2.me/theorems/58386beb-1dd9-4799-99e9-207e70787945
-- title:
--   Under ordinary RH the centered progression estimate is equivalent to a residue bias at perfect squares
-- statement:
--   Assume the ordinary Riemann hypothesis for the Riemann zeta function. For a positive modulus \(q\), unit class \(a\), and \(1/2<\sigma<1\), the centered bilinear Möbius sum has a bound \(C(N+1)^\sigma\) at every cutoff if and only if \(\varphi(q)=1\) or, at every perfect square \(u^2\), the deviation of the class sum from the average over unit classes has magnitude at most \(D(u^2+1)^\sigma\). The constants are independent of the cutoff. For moduli 1 and 2 the first alternative supplies the estimate directly.
-- source:
--   Combines the previously proved perfect-square interpolation https://prove2.me/theorems/b1cc026b-b5ab-5744-b1e2-eaee7b654e01 with the ordinary RH implication https://prove2.me/theorems/465491a6-91e2-4ec8-b3c7-95f64438963d and Dirichlet-prefix convergence https://prove2.me/theorems/17c42452-539d-4823-8913-e8718332764e. The centered target is https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.centered_moebius_bound_iff_square_residue_bias_of_riemannHypothesis
    (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ) ↔
    (q.totient = 1 ∨ ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ) := by sorry
