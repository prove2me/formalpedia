-- Prove2me | Theorems.Thm_L22EigEst_theorem_4
-- name    : L22EigEst.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:54.303656+00:00
-- url     : https://prove2.me/theorems/327860d2-8256-40f4-a921-1639d7bc6752
-- title:
--   Theorem 4 — all eigenvalues to $\pm\varepsilon\|A\|_F$ from $O(\log^{1.5}(1/\varepsilon)/\varepsilon^4)$ queries in an $O(\log(1/\varepsilon)/\varepsilon^2)$ principal submatrix
-- statement:
--   There are a constant $C$ and a randomized non-adaptive query algorithm in the $\ell_2^2$-sampling model with the following property. Let $n\ge0$, let $A\in\mathbb R^{n\times n}$ be symmetric with eigenvalues $\lambda_1(A)\ge\dots\ge\lambda_n(A)$, and let $\varepsilon\in(0,1/2)$. Given $n$, $\varepsilon$ and the squared row norms $\|A_1\|_2^2,\dots,\|A_n\|_2^2$, the algorithm draws a set $Q$ of positions and outputs $\hat\lambda_1,\dots,\hat\lambda_n\in\mathbb R$ from the entries of $A$ at $Q$. With probability at least $2/3$, all of the following hold at once:
--
--   1. the number of entries read is $|Q|\le C\,\log^{3/2}(1/\varepsilon)/\varepsilon^4$;
--   2. all of them lie in one principal submatrix of dimension at most $C\log(1/\varepsilon)/\varepsilon^2$: $Q\subseteq T\times T$ for some $T\subseteq[n]$ with $|T|\le C\log(1/\varepsilon)/\varepsilon^2$;
--   3. for every $i\in[n]$,
--
--   $$|\hat\lambda_i-\lambda_i(A)|\le\varepsilon\|A\|_F .$$
--
--   Neither bound depends on $n$. This answers the question of [Woo25], and with the lower bounds of the paper (Theorems 8 and 9) it shows that the optimal sample complexity is $\Theta(\log(1/\varepsilon)/\varepsilon^2)$.
--
--   Differences from the source:
--   - generalization: an algorithm with query access to A → a randomized non-adaptive algorithm: a distribution over query plans (Q, output map) that depends only on n, ε and the row norms, whose output sees A only at Q; reason: an existence claim for non-adaptive algorithms implies it for algorithms; the paper's algorithm is non-adaptive (p.4)
--   - encoding: the algorithm's randomness → a PMF over query plans; probability = toOuterMeasure; reason: countably supported randomness; the paper's algorithm uses finitely many coin flips
--   - encoding: query complexity = number of entries read; sample complexity = dimension of the smallest principal submatrix containing all queries → |Q| (ordered positions) and the size of some T with Q ⊆ T × T; reason: the definitions of p.3; a plan may read only one of (i, j), (j, i)
--   - reading: "with probability at least 2/3" followed by both bullets → one event containing the query bound, the submatrix bound and every eigenvalue bound; reason: the proof of Theorem 5 bounds the failure of all of them together (p.15)
--   - reading: O(log^1.5(1/ε)/ε⁴) and O(log(1/ε)/ε²) → one constant C, chosen before n, ε, A and the algorithm, for both bounds over ε ∈ (0, 1/2); reason: log(1/ε) > log 2 > 0 on the domain, so this is the asymptotic O as ε → 0; independence of n is the paper's claim
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 4, p.10

import Definitions.Def_L22EigEst_rowSq
import Definitions.Def_L22EigEst_QueryPlan
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Theorem 4** (p.10), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "There exists an algorithm which receives query access to a symmetric matrix A ∈ ℝ^{n×n},
an accuracy parameter ε ∈ (0, 1/2), and the squared row norms ∥A1∥2², . . . , ∥An∥2² of A, and returns
n scalars λ̂1, . . . , λ̂n ∈ ℝ such that with probability at least 2/3 • The algorithm has a query
complexity of O(log^1.5(1/ε)/ε⁴) entries of A, all of which lie in an O(log(1/ε)/ε²) × O(log(1/ε)/ε²)
sized principal sub-matrix of A. • For all i ∈ [n], the estimated eigenvalue λ̂i satisfies
|λ̂i − λi| ≤ ε∥A∥F."

**Formalization Note.**
* The algorithm is a `QueryAlg`: from `n`, `ε` and the row-norm list only, a `PMF` over
  non-adaptive query plans whose output sees `A` only at the queried positions `Q` (ordered pairs).
* The O(·) bounds are one constant `C`, chosen before `n`, `ε`, `A` and the algorithm, for both the
  query count `|Q|` and the side `|T|` of a principal submatrix `T × T ⊇ Q`; as `log(1/ε) > log 2 > 0`
  on `(0, 1/2)` this is the asymptotic O as `ε → 0`.
* One success event contains all three clauses.
* `gamma A hA i` is `λ_{i+1}(A)` (0-based, non-increasing). -/
theorem theorem_4 :
    ∃ C : ℝ, ∃ alg : QueryAlg, ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
      (ε : ℝ), 0 < ε → ε < 1 / 2 →
      (2 / 3 : ENNReal) ≤ (alg n ε (fun i => rowSq A i)).toOuterMeasure
        {P | (P.Q.card : ℝ) ≤ C * Real.log (1 / ε) ^ (3 / 2 : ℝ) / ε ^ 4 ∧
          (∃ T : Finset (Fin n), (T.card : ℝ) ≤ C * Real.log (1 / ε) / ε ^ 2 ∧ P.Q ⊆ T ×ˢ T) ∧
          ∀ i, |P.out (respond A P) i - gamma A hA i| ≤ ε * frob A} := by sorry

end L22EigEst
