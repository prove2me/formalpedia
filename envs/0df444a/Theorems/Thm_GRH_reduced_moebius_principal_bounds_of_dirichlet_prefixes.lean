-- Prove2me | Theorems.Thm_GRH_reduced_moebius_principal_bounds_of_dirichlet_prefixes
-- name    : GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T11:53:31.935595+00:00
-- url     : https://prove2.me/theorems/d5ab2d09-0f56-4b08-b160-bf32085f60bc
-- title:
--   Bounds for reduced harmonic and ordinary Möbius sums from an untwisted real Dirichlet prefix
-- statement:
--   Fix a positive modulus \(q\), an exponent \(1/2<\sigma<1\), and a uniform bound on the ordinary real prefixes \(\sum_{1\le j<n}\mu(j)j^{-\sigma}\). There is a single nonnegative constant \(K\) such that for every \(n\ge0\), the coprime harmonic sum \(H_q(n)\) has magnitude at most \(K(n+1)^{\sigma-1}\) and the coprime Möbius sum \(P_q(n)=\sum_{k\le n,(k,q)=1}\mu(k)\) has magnitude at most \(3K(n+1)^\sigma\).
-- source:
--   The harmonic transfer uses the four accepted inputs in https://prove2.me/submissions/fb5b50f4-8dbf-495b-999d-76118ada7f21. The reverse partial summation estimate here supplies the explicit principal constant 3K.

import Definitions.Def_GRH_MoebiusBilinear

open scoped BigOperators

theorem GRH.reduced_moebius_principal_bounds_of_dirichlet_prefixes
    (q : ℕ) [NeZero q] (σ B : ℝ) (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) (hB : 0 ≤ B)
    (hprefix : ∀ n : ℕ, |∑ j ∈ Finset.range n,
      (ArithmeticFunction.moebius j : ℝ) * (j : ℝ) ^ (-σ)| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ n : ℕ, |GRH.reducedMoebiusHarmonic q n| ≤ K * ((n : ℝ) + 1) ^ (σ - 1)) ∧
      (∀ n : ℕ, |∑ k ∈ Finset.range (n + 1),
        if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
        (3*K) * ((n : ℝ) + 1) ^ σ) := by sorry
