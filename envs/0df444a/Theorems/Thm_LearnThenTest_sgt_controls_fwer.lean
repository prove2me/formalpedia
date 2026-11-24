-- Prove2me | Theorems.Thm_LearnThenTest_sgt_controls_fwer
-- name    : LearnThenTest.sgt_controls_fwer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:12:39.107206+00:00
-- url     : https://prove2.me/theorems/02f89e91-e0d4-4db8-9494-b384e0047981
-- title:
--   Proposition 5: sequential graphical testing controls FWER
-- statement:
--   Let $\delta\in(0,1)$. Let $\delta_1,\dots,\delta_N\ge0$ be initial error budgets with $\sum_i\delta_i=\delta$. Let $g_{i,j}\in[0,1]$ be edge weights with $g_{i,i}=0$ and $\sum_jg_{i,j}\le1$ for every $i$. Then sequential graphical testing (Algorithm 2, Bretz et al. 2009) with this graph is an FWER-controlling algorithm at level $\delta$ in the sense of Definition 2. This holds for every rule that chooses which eligible hypothesis to reject at each step.
--
--   At each step the procedure rejects some unrejected $i$ with $p_i\le\delta_i$. It then passes $i$'s budget to its neighbours, $\delta_j\leftarrow\delta_j+\delta_ig_{i,j}$, and updates the graph, $g_{k,j}\leftarrow(g_{k,j}+g_{k,i}g_{i,j})/(1-g_{k,i}g_{i,k})$.
--
--   **Formalization Note** "Choose any $i$" is modelled by an arbitrary choice rule. The rule sees the current state and the set of eligible hypotheses, and it must return an eligible hypothesis. The loop condition is restricted to unrejected hypotheses. Read literally, the printed condition never terminates when a rejected hypothesis has $p_i=0$ (its level has been set to $0$), but such a step changes nothing. A $0/0$ in the weight update is read as $0$. The nonnegativity $\delta_i\ge0$ is implicit in the paper. The printed constraint $\sum_{j=1}^{n}g_{i,j}\le1$ has $n$ in place of $N$.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.3.2, Algorithm 2 and Proposition 5, p. 6

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem sgt_controls_fwer (N : ℕ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (δ0 : Fin N → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ0 i) (hsum : ∑ i, δ0 i = δ) (g : Fin N → Fin N → ℝ)
    (hg : ∀ i j, g i j ∈ Set.Icc (0 : ℝ) 1) (hgii : ∀ i, g i i = 0)
    (hgsum : ∀ i, ∑ j, g i j ≤ 1) (pick : SGTState N → Finset (Fin N) → Fin N)
    (hpick : ∀ s S, S.Nonempty → pick s S ∈ S) :
    IsFWERControlling N δ (sgt N pick δ0 g) := by sorry

end LearnThenTest
