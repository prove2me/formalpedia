-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_algorithm_protocol_realization
-- name    : LindbladTolerant.Testing.algorithm_protocol_realization
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:21.52756+00:00
-- url     : https://prove2.me/theorems/7b1d279c-d695-4619-ba3e-cd0be67f0108
-- title:
--   Algorithm 1 — admissible protocol realization
-- statement:
--   For every admissible parameter tuple, the explicitly defined physical Algorithm 1 is realized by one forward-evolution protocol. The protocol has exactly the prescribed number of queries, its summed durations on every branch are at most the prescribed total time, and its Born output distribution agrees with the finite flag-history formula `algorithmProbability` on every source generator.
--
--   This isolates the circuit-and-instrument implementation part of Theorem 5.1 from its probabilistic correctness proof. It allows initial classical randomness, stored quantum outputs, and the fixed copy-estimator routine, while charging all $M$ attempts, including failed preparations.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238, Section 3 oracle model, p.16, Algorithm 1 and Theorem 5.1, pp.26–28, especially the cost paragraph after Eq.(109).

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

theorem LindbladTolerant.Testing.algorithm_protocol_realization {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (bound eps1 eps2 : ℝ) (hbound : 0 < bound) (he1 : 0 ≤ eps1)
    (he12 : eps1 < eps2) (he2 : eps2 ≤ bound / Real.sqrt 2) :
    ∃ p : Protocol n ℕ, Admissible p ∧
      p.queries = attemptCount k bound eps1 eps2 ∧
      TimeAtMost p (totalTime k eps1 eps2) ∧
      ∀ g, SourceClass k bound g → ∀ b : Bool,
        outputProbability p g b = ENNReal.ofReal (algorithmProbability k bound eps1 eps2 g b) := by sorry
