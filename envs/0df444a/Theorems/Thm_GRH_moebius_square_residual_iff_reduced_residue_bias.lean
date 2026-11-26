-- Prove2me | Theorems.Thm_GRH_moebius_square_residual_iff_reduced_residue_bias
-- name    : GRH.moebius_square_residual_iff_reduced_residue_bias
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:53:32.430744+00:00
-- url     : https://prove2.me/theorems/cd6ea8c1-8edb-43b9-94b8-520f807b2183
-- title:
--   The square Mertens residual reduces to deviation from the reduced-residue mean
-- statement:
--   Write \(M_a(X)=\sum_{k\le X,\ k\equiv a\pmod q}\mu(k)\), \(P_q(X)=\sum_{k\le X,(k,q)=1}\mu(k)\), and \(H_q(u)=\sum_{k\le u,(k,q)=1}\mu(k)/k\). Fix a unit class and \(1/2<\sigma<1\). Suppose the ordinary prefixes of \(\sum\mu(j)j^{-\sigma}\) are bounded. Then \(M_a(u^2)+(u^2/q)H_q(u)^2=O((u^2+1)^\sigma)\) uniformly in \(u\) if and only if the modulus has one unit class or \(M_a(u^2)-P_q(u^2)/\varphi(q)=O((u^2+1)^\sigma)\). With one unit class the deviation is identically zero.
-- source:
--   Specializes the signed square residual at https://prove2.me/theorems/4267fa34-f5fc-4de7-a1fd-d4169b15fa7e. The square-root weight estimate also appears in https://prove2.me/submissions/0176d409-98bf-44bc-b6fe-85633680ae6d.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.moebius_square_residual_iff_reduced_residue_bias
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ B : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) (hB : 0 ≤ B)
    (hprefix : ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B) :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ) ↔
    (q.totient = 1 ∨ ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) - (∑ k ∈ Finset.range (u ^ 2 + 1),
          if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) / (q.totient : ℝ)| ≤ D * ((u : ℝ) ^ 2 + 1) ^ σ) := by sorry
