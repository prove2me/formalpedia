-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_1_3_geometric
-- name    : KSATSingleFlip.Connect.theorem_1_3_geometric
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T07:18:31.669591+00:00
-- url     : https://prove2.me/theorems/38e7d9c0-5a48-4402-abc1-2d90096c3d5b
-- title:
--   Geometric consequences of the looseness–rigidity transition
-- statement:
--   This is the geometric consequence of Theorem 1.3, without the theorem's deterministic algorithm or runtime clauses. Let $\alpha_-(k)$ and $\alpha_+(k)$ be the two density endpoints in (1.5), with the $-8$ and $+8$ corrections respectively.
--
--   For all sufficiently large fixed $k$ and sufficiently large $n$, uniformly in the density, the following statements hold with probability at least $1-1/n$. Below $\alpha_-(k)$, the formula is satisfiable and a single set of at least $1-1/n$ solution mass has both properties: every variable can be reversed along a satisfying path of at most $32(\ln k)^5\ln n$ flips, and every solution in a Hamming ball of radius $c_k n$ is connected by a satisfying path of at most $Cn$ flips. Here $c_k>0$ and $C$ is absolute.
--
--   From $\alpha_+(k)$ up to $2^k(\ln2-1/\ln k)$, the formula is satisfiable and all but an $e^{-c'_k n}$ fraction of solutions have at least $(1-\delta_k)n$ variables such that reversing any of them requires changing at least $d_k n$ variables, where $c'_k,d_k>0$ and $\delta_k\to0$. This supporting target does not assert the constructive or running-time parts of Theorem 1.3.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, geometric parts of Theorem 1.3 and (1.5), printed p. 4 (PDF p. 6), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_LoosenessRigidity

open scoped Classical BigOperators
open Filter Topology

namespace KSATSingleFlip.Connect

/-- The geometric consequences of Theorem 1.3; the algorithmic runtime and
constructibility clauses are separate from this target. -/
theorem theorem_1_3_geometric :
    ∃ pathConstant : ℝ, 0 < pathConstant ∧
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃ looseRadius rigidRadius exceptionRate : ℝ,
        0 < looseRadius ∧ 0 < rigidRadius ∧ 0 < exceptionRate ∧
        ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
          ((m : ℝ) / n ≤ geometryDensity k false →
            1 - 1 / (n : ℝ) ≤ formulaProb n k m (fun F =>
              HasLooseLocalGeometry k (ofFormula F) looseRadius pathConstant)) ∧
          (geometryDensity k true ≤ (m : ℝ) / n →
            (m : ℝ) / n ≤ (2 : ℝ)^k * (Real.log 2 - 1 / Real.log k) →
            1 - 1 / (n : ℝ) ≤ formulaProb n k m (fun F =>
              HasRigidGeometry (ofFormula F) (δ k) rigidRadius exceptionRate)) := by
  sorry

end KSATSingleFlip.Connect
