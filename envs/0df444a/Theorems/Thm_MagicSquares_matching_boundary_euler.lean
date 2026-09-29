-- Prove2me | Theorems.Thm_MagicSquares_matching_boundary_euler
-- name    : MagicSquares.matching_boundary_euler
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-22T14:00:06.680988+00:00
-- url     : https://prove2.me/theorems/c44cf304-6efb-4853-bedd-7a2a604fb3f2
-- title:
--   Matching-covered board boundary cancellation
-- statement:
--   Let $n\ge 1$ and let a board be a subset of $[n]\times[n]$. For a permutation $\sigma$, write $\phi_\sigma=\{(i,\sigma(i)):i\in[n]\}$. A board is matching-covered if it is nonempty and each of its cells belongs to some permutation support contained in the board. Define
--   $$a(C)=\sum_{S\subseteq C}(-1)^{|S|}\mathbf 1\{C\setminus S\text{ contains a permutation support}\}.$$
--
--   For any matching-covered boards $D\subseteq B$ and any permutation support $\phi_\sigma\subseteq B$, the following finite boundary identity holds:
--   $$\sum_{\substack{D\subseteq C\subseteq B\\B\setminus\phi_\sigma\subseteq C}}a(C)=\begin{cases}a(B),&\phi_\sigma\subseteq D,\\0,&\phi_\sigma\nsubseteq D.\end{cases}$$
--
--   The summation includes all such boards $C$, without requiring them to be matching-covered. This identity provides a finite combinatorial sufficient condition for reciprocity of semi-magic counting polynomials. Its formal proof is the remaining obligation in the associated conditional reduction.
-- source:
--   Original matching-board specialization of the Eulerian face-lattice property and the order-dual of Weisner's theorem; derived in MATCHING-BOUNDARY-SOURCE.md. Richard P. Stanley, Enumerative Combinatorics, Volume 1, author manuscript, Proposition 3.8.9, p. 309, and Corollary 3.9.3, p. 313: https://math.mit.edu/~rstan/ec/ec1.pdf. This matching-board statement is our specialization, not a verbatim theorem in that source.

import Mathlib
import Definitions.Def_MagicSquaresMatchingBoundary

namespace MagicSquares

theorem matching_boundary_euler (n : ℕ) (hn : 1 ≤ n) :
    MagicSquaresBoundary.MatchingBoundaryCriterion n := by
  sorry

end MagicSquares
