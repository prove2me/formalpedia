-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_lemma_7_7
-- name    : MongeApprox.Sparsify.lemma_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:03:03.076309+00:00
-- url     : https://prove2.me/theorems/76b6ae5a-e183-4671-a7e6-542b5fb28164
-- title:
--   Lemma 7.7 — the recursively sparsified simple matrix keeps κ, approximates A, and has core O((n/√ε) log n log(2 + min{K, κ(A)}))
-- statement:
--   There is $C>0$ such that the following holds. Let $A$ be a simple Monge matrix of size $p\times q$ with $p,q\in[2..n]$, let $K\in[0,+\infty]$ and $\varepsilon\in(0,1]$, and let $\widehat A$ be the matrix of the recursive partition (15) with the staircase replacement of Lemma 7.5 on every leaf of positive mass. Then $\widehat A$ is a simple Monge matrix with: 1. $\kappa(\widehat A)=\kappa(A)$; 2. $A_{ij}\le\widehat A_{ij}$ for all entries, $\widehat A_{ij}=0$ whenever $A_{ij}=0$, and $\widehat A_{ij}\le A_{ij}+\varepsilon\max\{1,A_{ij}\}$ whenever $A_{ij}\le K$; 3. $\delta(\widehat A)\le C\cdot\frac{n}{\sqrt\varepsilon}\log n\cdot\log(2+\min\{K,\kappa(A)\})$.
--
--   Differences from the source:
--   - reading: we obtain µ̂ by applying Lemma 7.5 to the leaves of positive mass → µ̂ is the staircase construction of Lemma 7.5's proof on each such leaf (`sparsify`); reason: the replacement the paper's proof of Lemma 7.5 constructs; Lemma 7.7 is about that matrix
--   - encoding: K ∈ [0, +∞], ε ∈ (0, 1] (parameters of Theorem 7.3) → K : ℝ≥0∞; hypotheses 0 < ε ≤ 1; reason: the section's standing parameters
--   - encoding: δ(Â) ∈ O(…) → ∃ C > 0, fixed before n, p, q, A, K, ε, with δ(Â) ≤ C·(…); reason: explicit constant for O(·)
--   - encoding: log (base unspecified, inside O(·)) → `Real.log` (natural logarithm); reason: inside O(·) the base changes only the constant C
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Lemma 7.7, printed pp. 37–38 (PDF 39–40); setup 'Recursive partition', printed p. 37 (PDF 39)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Quadrant
import Definitions.Def_MongeApprox_Sparsify_Partition

namespace MongeApprox.Sparsify

open scoped ENNReal

/-- Lemma 7.7. There is `C > 0` such that for every simple Monge `p × q` matrix `A` with
`p, q ∈ [2..n]`, every `K ∈ [0, +∞]` and every `ε ∈ (0, 1]`, the matrix `Â = sparsify A K ε` of the
recursive partition (15) with the staircase replacement on every leaf of positive mass is a simple
Monge matrix with: 1. `κ(Â) = κ(A)`; 2. `A_ij ≤ Â_ij` for all entries, `Â_ij = 0` whenever
`A_ij = 0`, and `Â_ij ≤ A_ij + ε · max{1, A_ij}` whenever `A_ij ≤ K`;
3. `δ(Â) ≤ C · (n/√ε) · log n · log(2 + min{K, κ(A)})`. -/
theorem lemma_7_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n p q : ℕ) (A : Matrix (Fin p) (Fin q) ℝ) (K : ℝ≥0∞) (ε : ℝ),
        2 ≤ p → p ≤ n → 2 ≤ q → q ≤ n → 0 < ε → ε ≤ 1 → IsSimple A →
        IsSimple (sparsify A K ε) ∧
        totalCurvature (sparsify A K ε) = totalCurvature A ∧
        (∀ i j, A i j ≤ sparsify A K ε i j) ∧
        (∀ i j, A i j = 0 → sparsify A K ε i j = 0) ∧
        (∀ i j, LeThreshold (A i j) K → sparsify A K ε i j ≤ A i j + ε * max 1 (A i j)) ∧
        (coreSize (sparsify A K ε) : ℝ) ≤
          C * ((n : ℝ) / Real.sqrt ε * Real.log n *
            Real.log (2 + minThreshold K (totalCurvature A))) := by sorry

end MongeApprox.Sparsify
