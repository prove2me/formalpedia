-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_eliminated_ge_half_degree_sum
-- name    : LubyMIS.MonteCarlo.eliminated_ge_half_degree_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:52:14.524259+00:00
-- url     : https://prove2.me/theorems/de86e0c3-312d-424f-b52b-6d24336b34cd
-- title:
--   Proof of Theorem 1, first display — E[Y_k − Y_{k+1}] ≥ ½·Σ d(i)·Pr[i ∈ I′ ∪ N(I′)] ≥ ½·Σ d(i)·Pr[i ∈ N(I′)]
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph, and let $I'$ be a random subset of $V'$ with an arbitrary finite distribution: $I' = S(\omega)$ with probability $w(\omega)$, where $w \ge 0$ and $\sum_\omega w(\omega) = 1$. Let $\mathrm{elim}(I')$ be the number of edges of $G'$ with at least one endpoint in $I' \cup N(I')$. Then
--   $$E\big[\mathrm{elim}(I')\big] \;\ge\; \frac12 \sum_{i \in V'} d(i)\, \Pr\big[i \in I' \cup N(I')\big] \;\ge\; \frac12 \sum_{i \in V'} d(i)\, \Pr\big[i \in N(I')\big].$$
--
--   This is the first step of the proof of Theorem 1: it reduces the expected number of eliminated edges to per-vertex probabilities, which Lemmas A and B bound. It uses nothing about how $I'$ is chosen, so it applies to Algorithm A, Algorithm B and the derandomized Algorithm D alike.
--
--   **Formalization Note** The paper states the display for Algorithm B's $I'$. It is formalized for an arbitrary finite random choice of $I'$, which contains both Algorithm A's and Algorithm B's laws as instances. Probabilities are written as $\Pr[i \in \cdot\,] = \sum_\omega w(\omega)\,[i \in S(\omega)]$. The two inequalities of the display are the two conjuncts.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1041, §3.4, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- First display of the proof of Theorem 1 (Luby 1986, §3.4, p. 1041), for an arbitrary random
selection `I′ = S ω` drawn with probabilities `w ω`:
`E[Y_k − Y_{k+1}] ≥ ½ ∑_i d(i) Pr[i ∈ I′ ∪ N(I′)] ≥ ½ ∑_i d(i) Pr[i ∈ N(I′)]`. -/
theorem eliminated_ge_half_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (S : Ω → Finset V) :
    (∑ ω, w ω * (eliminated H (S ω) : ℝ)) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ nbhd H (S ω) then w ω else 0) := by sorry

end LubyMIS.MonteCarlo
