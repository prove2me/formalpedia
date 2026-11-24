-- Prove2me | Theorems.Thm_LearnThenTest_fixed_sequence_controls_fwer
-- name    : LearnThenTest.fixed_sequence_controls_fwer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:11:37.036039+00:00
-- url     : https://prove2.me/theorems/1860faf3-d84c-4394-88ee-049232e9cc92
-- title:
--   Proposition 3: fixed sequence testing controls FWER
-- statement:
--   Let $\delta\in(0,1)$ and let $\mathcal J\subseteq\{1,\dots,N\}$ be a set of initializations. Fixed sequence testing (Algorithm 1) runs as follows. For each $j\in\mathcal J$ not already rejected, it rejects $j,j+1,\dots$ for as long as the current p-value is at most $\delta/|\mathcal J|$, and it stops at the first acceptance or at index $N$. This procedure is an FWER-controlling algorithm at level $\delta$ in the sense of Definition 2.
--
--   Single-start fixed sequence testing ($|\mathcal J|=1$) needs no multiplicity correction. It is the procedure the paper recommends when the risk is nearly monotone in $\lambda$.
--
--   **Formalization Note** The `while` loop of Algorithm 1 is stopped at the last index $N$, where the printed loop would read the undefined $p_{N+1}$. Initializations are visited in increasing order.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.3.1, Algorithm 1 and Proposition 3, p. 5; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem fixed_sequence_controls_fwer (N : ℕ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (J : Finset (Fin N)) : IsFWERControlling N δ (fixedSeq N δ J) := by sorry

end LearnThenTest
