-- Prove2me | Theorems.Thm_HighDimStat_SparseLinear_pairwise_incoherence_implies_restricted_nullspace
-- name    : HighDimStat.SparseLinear.pairwise_incoherence_implies_restricted_nullspace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:58.179213+00:00
-- url     : https://prove2.me/theorems/40b395fc-6c07-4e89-bac8-944d6bef206b
-- title:
--   Small pairwise incoherence implies the restricted nullspace property
-- statement:
--   **Proposition 7.9.** A simply-checked bound on the pairwise incoherence of $X$ is
--   sufficient to guarantee the restricted nullspace property uniformly over every support
--   set of a given sparsity.
--
--   For $X \in \mathbb R^{n\times d}$ and $s \in \mathbb N$, if
--
--   $$
--   \delta_{PW}(X) \;\le\; \frac{1}{3s},
--   $$
--
--   then the restricted nullspace property holds for every $S \subseteq \{1,\dots,d\}$ with
--   $|S| \le s$.
--
--   Combined with Theorem 7.8, this gives a directly verifiable sufficient condition —
--   depending only on pairwise column correlations of $X$, not on the geometry of the whole
--   cone $C(S)$ — for the basis pursuit program to exactly recover every $s$-sparse vector.
--
--   **Formalization Note** $s$ is a natural number, so $1/(3s)$ is Mathlib's junk value $0$ at
--   $s=0$; the hypothesis then forces $\delta_{PW}(X)=0$ exactly, and the conclusion ranges
--   only over $S=\varnothing$ (the only set of cardinality $\le 0$), for which the restricted
--   nullspace property holds unconditionally — so the $s=0$ corner introduces neither a false
--   nor a vacuously-strengthened instance of the book's claim, which is stated for $s \ge 1$.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 203 (PDF p. 223), Proposition 7.9, Eq. (7.13)

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_PairwiseIncoherence
import Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty

namespace HighDimStat.SparseLinear

/-- **Proposition 7.9**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.13), p. 203.
If the pairwise incoherence satisfies `δ_PW(X) ≤ 1/(3s)`, then the restricted nullspace
property holds for all subsets `S` of cardinality at most `s`. -/
theorem pairwise_incoherence_implies_restricted_nullspace {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (h : pairwiseIncoherence X ≤ 1 / (3 * (s : ℝ))) :
    ∀ S : Finset (Fin d), S.card ≤ s → RestrictedNullspaceProperty X S := by sorry

end HighDimStat.SparseLinear
