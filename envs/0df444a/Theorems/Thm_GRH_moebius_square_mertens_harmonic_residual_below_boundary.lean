-- Prove2me | Theorems.Thm_GRH_moebius_square_mertens_harmonic_residual_below_boundary
-- name    : GRH.moebius_square_mertens_harmonic_residual_below_boundary
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T11:07:14.861472+00:00
-- url     : https://prove2.me/theorems/4267fa34-f5fc-4de7-a1fd-d4169b15fa7e
-- title:
--   Möbius cancellation against the harmonic-square correction at square cutoffs below the exponent boundary
-- statement:
--   Fix a positive modulus \(q\), a unit residue \(a\), and \(1/2<\sigma\le0.8749570698\). The open estimate asks for a constant \(D\ge0\) such that for every nonnegative integer \(u\),
--   \[
--   \left|\sum_{k\le u^2,\ k\equiv a\bmod q}\mu(k)
--   +\frac{u^2}{q}\left(\sum_{1\le d\le u,\ (d,q)=1}\frac{\mu(d)}{d}\right)^2\right|
--   \le D(u^2+1)^\sigma.
--   \]
--   The residue sum is evaluated only at perfect squares. The harmonic term and the Möbius sum retain their relative sign. This residual is proposed as the remaining analytic input for the centered progression estimate.
-- source:
--   Proposed square-endpoint subproblem of https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006. The previously verified upper exponent interval is the second conclusion of https://prove2.me/theorems/caa25386-7d4a-41b1-afe7-db19fdae4d1e. The finite reindexing comes from Helfgott and Thompson, Summing μ(n): a faster elementary algorithm, §2, (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.moebius_square_mertens_harmonic_residual_below_boundary
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hrecord : σ ≤ (0.8749570698 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ := by sorry
