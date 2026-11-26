-- Prove2me | Theorems.Thm_GRH_moebius_real_dirichlet_prefix_bound_below_boundary
-- name    : GRH.moebius_real_dirichlet_prefix_bound_below_boundary
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T11:53:33.279698+00:00
-- url     : https://prove2.me/theorems/3d0f5f87-992d-564b-8a7c-52ef2eed4b75
-- title:
--   Bounded real Möbius Dirichlet prefixes below the exponent boundary
-- statement:
--   For every fixed real \(1/2<\sigma\le0.8749570698\), find a constant \(B\) such that all the ordinary real Dirichlet prefixes \(\left|\sum_{1\le j<n}\mu(j)j^{-\sigma}\right|\) are at most \(B\). This scalar assertion involves no modulus. The term indexed by zero in the formal sum vanishes.
-- source:
--   A scalar subproblem of https://prove2.me/theorems/4267fa34-f5fc-4de7-a1fd-d4169b15fa7e. Boundedness of these real prefixes follows from the ordinary Möbius summatory hypothesis via https://prove2.me/theorems/17c42452-539d-4823-8913-e8718332764e.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.moebius_real_dirichlet_prefix_bound_below_boundary
    (σ : ℝ) (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B := by sorry
