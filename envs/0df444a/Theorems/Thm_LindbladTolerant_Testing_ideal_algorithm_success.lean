-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_ideal_algorithm_success
-- name    : LindbladTolerant.Testing.ideal_algorithm_success
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:01.643335+00:00
-- url     : https://prove2.me/theorems/eeffe8d4-00d4-44c2-a99e-d91a5f59afb6
-- title:
--   Theorem 5.1 — ideal Algorithm 1 success probability
-- statement:
--   Consider Algorithm 1 with each finite-time preparation replaced by the ideal flagged state of Eq.(95). On the low-strength promise its YES probability, and on the high-strength promise its NO probability, are both at least
--
--   $$
--   1-\left(\frac1{32}+\frac1{100}\right).
--   $$
--
--   This is the ideal-experiment component of Theorem 5.1. The two error terms are the Chebyshev bound for the empirical jump rate and the conditional failure bound of the copy estimator. The statement covers zero jump rate, where every preparation fails, and the high-rate case $\Gamma>4\varepsilon_2$ separately.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Theorem 5.1 proof, pp.26–27, Eqs.(96)–(105).

import Definitions.Def_LindbladTolerant_Testing_ideal_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

theorem LindbladTolerant.Testing.ideal_algorithm_success {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (bound eps1 eps2 : ℝ) (hbound : 0 < bound) (he1 : 0 ≤ eps1)
    (he12 : eps1 < eps2) (he2 : eps2 ≤ bound / Real.sqrt 2)
    (g : Super (Qubits n) (Qubits n)) (hg : SourceClass k bound g) :
    (frobenius (canonicalD g) ≤ eps1 →
      1 - (1/32 + 1/100) ≤ idealAlgorithmProbability k bound eps1 eps2 g true) ∧
    (eps2 ≤ frobenius (canonicalD g) →
      1 - (1/32 + 1/100) ≤ idealAlgorithmProbability k bound eps1 eps2 g false) := by sorry
