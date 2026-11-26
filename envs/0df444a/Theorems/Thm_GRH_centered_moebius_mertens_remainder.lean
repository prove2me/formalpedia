-- Prove2me | Theorems.Thm_GRH_centered_moebius_mertens_remainder
-- name    : GRH.centered_moebius_mertens_remainder
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:07:13.024892+00:00
-- url     : https://prove2.me/theorems/99bde901-b30d-40ce-ae0f-029719b78029
-- title:
--   Exact square-root remainder for the centered Möbius progression sum
-- statement:
--   For any positive modulus \(q\), any residue \(a\), and any \(N\ge0\), let \(U=\lfloor\sqrt N\rfloor\), \(M_a(X)=\sum_{1\le k\le X,\ k\equiv a\pmod q}\mu(k)\), and \(H_q(U)=\sum_{1\le d\le U,\ (d,q)=1}\mu(d)/d\). If \(B_a(N)\) denotes the centered bilinear expression, then
--   \[
--    B_a(N)+M_a(N)+(N/q)H_q(U)^2=2M_a(U).
--   \]
--   The absolute value of this remainder is at most \(2U\). The equality holds also for nonunit residues and at \(N=0\).
-- source:
--   Helfgott and Thompson, Summing μ(n): a faster elementary algorithm, §2, (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. The residue-weighted truncation and the centering factorization are adapted from the public proof sources https://prove2.me/submissions/509e229b-7ae5-4fe8-b643-d32c7895621a and https://prove2.me/submissions/0176d409-98bf-44bc-b6fe-85633680ae6d. The combined centered identity also appears inside https://prove2.me/theorems/caa25386-7d4a-41b1-afe7-db19fdae4d1e. The statement here supplies an independently reusable remainder bound for every residue.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.centered_moebius_mertens_remainder
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    let M := fun X : ℕ => ∑ k ∈ Finset.range (X + 1),
      if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0
    let E := GRH.centeredMoebiusBilinear q a N +
      (M N + (1 / (q : ℝ)) * (N : ℝ) * (GRH.reducedMoebiusHarmonic q N.sqrt) ^ 2)
    E = 2 * M N.sqrt ∧ |E| ≤ 2 * (N.sqrt : ℝ) := by sorry
