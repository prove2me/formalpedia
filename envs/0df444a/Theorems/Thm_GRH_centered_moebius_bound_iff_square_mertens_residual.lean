-- Prove2me | Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
-- name    : GRH.centered_moebius_bound_iff_square_mertens_residual
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:07:12.058631+00:00
-- url     : https://prove2.me/theorems/b1cc026b-b5ab-5744-b1e2-eaee7b654e01
-- title:
--   The centered Möbius power bound is equivalent to a Mertens residual at perfect squares
-- statement:
--   For every positive modulus \(q\), residue \(a\), and real exponent \(\sigma\ge1/2\), the following two estimates are equivalent. The centered bilinear sum \(B_a(N)\) is \(O((N+1)^\sigma)\) at every nonnegative integer \(N\). At the square cutoffs alone, \(M_a(u^2)+(u^2/q)H_q(u)^2\) is \(O((u^2+1)^\sigma)\). Here \(M_a(X)\) is the sum of \(\mu(k)\) over positive \(k\le X\) in residue class \(a\), and \(H_q(u)=\sum_{1\le d\le u,(d,q)=1}\mu(d)/d\). The assertion includes nonunit residues, \(u=0\), and the exponent \(1/2\).
-- source:
--   The finite truncation and centering come from https://prove2.me/submissions/509e229b-7ae5-4fe8-b643-d32c7895621a and https://prove2.me/submissions/0176d409-98bf-44bc-b6fe-85633680ae6d. This equivalence follows by interpolating the signed one-dimensional residual between square cutoffs. It applies to the target https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.centered_moebius_bound_iff_square_mertens_residual
    (q : ℕ) [NeZero q] (a : ZMod q) (σ : ℝ) (hhalf : (1/2 : ℝ) ≤ σ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ) ↔
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u : ℕ,
      |(∑ k ∈ Finset.range (u ^ 2 + 1),
          if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (u : ℝ) ^ 2 * ((1 / (q : ℝ)) * (GRH.reducedMoebiusHarmonic q u) ^ 2)| ≤
      D * ((u : ℝ) ^ 2 + 1) ^ σ := by sorry
