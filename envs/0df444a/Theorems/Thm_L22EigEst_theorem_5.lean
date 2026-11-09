-- Prove2me | Theorems.Thm_L22EigEst_theorem_5
-- name    : L22EigEst.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:13.131554+00:00
-- url     : https://prove2.me/theorems/cf29fca9-567f-4119-9b12-19cdf622e850
-- title:
--   Theorem 5 — under Definition 3.1, all eigenvalues to $\pm5\varepsilon\|A\|_F$ from $O(\log^{1.5}(1/\varepsilon)/\varepsilon^4)$ queries
-- statement:
--   There is a constant $c_0$ such that for every $c\ge c_0$ there are a constant $C$ and a randomized non-adaptive query algorithm in the $\ell_2^2$-sampling model with the following property. Let $n\ge0$, let $A\in\mathbb R^{n\times n}$ be symmetric, and let $\varepsilon\in(0,1/4)$. Suppose $A$ has bounded row norms (Definition 3.1) with $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$:
--
--   $$\forall i:\quad s\|A_i\|_2^2\le\|A\|_F^2 .$$
--
--   Given $n$, $\varepsilon$ and $\|A_1\|_2^2,\dots,\|A_n\|_2^2$, the algorithm draws a set $Q$ of positions and outputs $\hat\lambda_1,\dots,\hat\lambda_n$ from the entries of $A$ at $Q$. With probability at least $2/3$, all of the following hold at once:
--
--   1. $|Q|\le C\log^{3/2}(1/\varepsilon)/\varepsilon^4$;
--   2. $Q\subseteq T\times T$ for some $T\subseteq[n]$ with $|T|\le C\log(1/\varepsilon)/\varepsilon^2$;
--   3. for every $i\in[n]$, $|\hat\lambda_i-\lambda_i(A)|\le5\varepsilon\|A\|_F$, where $\lambda_1(A)\ge\dots\ge\lambda_n(A)$.
--
--   The algorithm is Algorithm 1. Theorem 4 follows by applying it to the matrix $VAV^\top$ of Algorithm 2.
--
--   Differences from the source:
--   - generalization: an algorithm with query access to A → a randomized non-adaptive algorithm: a distribution over query plans (Q, output map) that depends only on n, ε and the row norms, whose output sees A only at Q; reason: an existence claim for non-adaptive algorithms implies it for algorithms; the paper's algorithm is non-adaptive (p.4)
--   - encoding: the algorithm's randomness → a PMF over query plans; probability = toOuterMeasure; reason: countably supported randomness; the paper's algorithm uses finitely many coin flips
--   - encoding: query complexity = number of entries read; sample complexity = dimension of the smallest principal submatrix containing all queries → |Q| (ordered positions) and the size of some T with Q ⊆ T × T; reason: the definitions of p.3; a plan may read only one of (i, j), (j, i)
--   - reading: "with probability at least 2/3" followed by both bullets → one event containing the query bound, the submatrix bound and every eigenvalue bound; reason: the proof of Theorem 5 bounds the failure of all of them together (p.15)
--   - reading: "Given a symmetric matrix A … there exists an algorithm" → the algorithm (and C) is chosen before n, A and ε; reason: the algorithm receives only query access and the row norms, so it cannot depend on A; this is the stronger reading
--   - generalization: "s = ⌈c log(1/ε)/ε²⌉ for some constant c" (Definition 3.1, Algorithm 1) → every c ≥ c₀; reason: every use of "c sufficiently large" in §4 is a lower bound on c; the statement for some c follows
--   - reading: O(·) bounds → one constant C, chosen after c and before n, ε, A, for both bounds over ε ∈ (0, 1/4); reason: log(1/ε) > log 4 > 0 on the domain, so this is the asymptotic O as ε → 0; C does not depend on n
--   - encoding: Definition 3.1, s‖A_i‖₂²/‖A‖_F² ≤ 1 → BoundedRowNorm (sParam c ε) A, i.e. s‖A_i‖₂² ≤ ‖A‖_F²; reason: multiplied out; equivalent for A ≠ 0
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 5, pp.10–11

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_QueryPlan
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Theorem 5** (Algorithm assuming Definition 3.1, pp.10–11), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Given a symmetric matrix A ∈ ℝ^{n×n} and
parameter ε ∈ (0, 1/4), there exists an algorithm which receives query access to A and the squared
row norms ∥A1∥2², . . . , ∥An∥2² of A, such that if Definition 3.1 is satisfied, then the algorithm
returns n scalars λ̂1, . . . , λ̂n ∈ ℝ such that with probability at least 2/3 • The algorithm only
queries O(log^1.5(1/ε)/ε⁴) entries of A, all of which lie in an O(log(1/ε)/ε²) × O(log(1/ε)/ε²) sized
principal sub-matrix of A. • For all i ∈ [n], the estimated eigenvalue λ̂i satisfies
|λ̂i − λi| ≤ 5ε∥A∥F."

**Formalization Note.**
* Same query model as Theorem 4 (`QueryAlg`, non-adaptive plans, output seeing only `Q`).
* The constant `c` of Definition 3.1 is the algorithm's constant: the statement holds for every
  `c ≥ c₀` (every "sufficiently large c" in §4 is a lower bound on `c`); `C` and the algorithm
  may depend on `c`, never on `n`, `A` or `ε`.
* Definition 3.1 is `BoundedRowNorm (sParam c ε) A`. One success event, as in Theorem 4. -/
theorem theorem_5 :
    ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ, ∃ alg : QueryAlg,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (ε : ℝ),
      0 < ε → ε < 1 / 4 → BoundedRowNorm (sParam c ε) A →
      (2 / 3 : ENNReal) ≤ (alg n ε (fun i => rowSq A i)).toOuterMeasure
        {P | (P.Q.card : ℝ) ≤ C * Real.log (1 / ε) ^ (3 / 2 : ℝ) / ε ^ 4 ∧
          (∃ T : Finset (Fin n), (T.card : ℝ) ≤ C * Real.log (1 / ε) / ε ^ 2 ∧ P.Q ⊆ T ×ˢ T) ∧
          ∀ i, |P.out (respond A P) i - gamma A hA i| ≤ 5 * ε * frob A} := by sorry

end L22EigEst
