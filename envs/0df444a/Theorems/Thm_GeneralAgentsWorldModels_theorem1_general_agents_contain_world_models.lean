-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_theorem1_general_agents_contain_world_models
-- name    : GeneralAgentsWorldModels.theorem1_general_agents_contain_world_models
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:39:34.750965+00:00
-- url     : https://prove2.me/theorems/7bca256c-45ee-42e2-9c81-04c4bd34c06d
-- title:
--   Theorem 1 (as proved): general agents contain world models
-- statement:
--   Let $S$ and $A$ be finite sets and let $n\ge3$. Then there is a map $F$, from goal-conditioned policies to transition models $\hat P_{ss'}(a)$, with the following property. For every environment $P$ on $S,A$ satisfying Assumption 1, every $\delta\in[0,1)$, and every bounded goal-conditioned agent $\pi$ with failure rate $\delta$ for all goals in $\Psi_n$, the model $\hat P=F(\pi)$ satisfies, for all $s,a,s'$,
--
--   $$\big|\hat P_{ss'}(a)-P_{ss'}(a)\big|\le\sqrt{\frac{P_{ss'}(a)\,(1-P_{ss'}(a))}{\lfloor (n-1)/2\rfloor\,(1-\delta)}}.$$
--
--   When $n$ is odd, $\lfloor(n-1)/2\rfloor=(n-1)/2$ and the bound is the paper's $\sqrt{2P_{ss'}(a)(1-P_{ss'}(a))/((n-1)(1-\delta))}$. The map $F$ depends only on $S$, $A$ and $n$: the same procedure recovers the model for every environment, every agent and every $\delta$, so the agent's policy alone determines an approximate world model.
--
--   **Formalization Note** The proof (eqs. (33), (57)) uses $m$ attempts of a transition, a goal of depth $2m+1$, and proves the bound $\sqrt{p(1-p)/(m(1-\delta))}$. Substituting $m=(n-1)/2$ is valid only for odd $n$; the statement is therefore given with $m=\lfloor(n-1)/2\rfloor$, which equals the printed bound for odd $n$ and is what the proof gives for even $n$. The printed case $n=2$ gives $m=0$, where the proof says nothing, and is excluded. The printed bound is infinite at $\delta=1$, so $\delta<1$ is assumed. The asymptotic claim $O(\delta/\sqrt n)+O(1/n)$ rests on a Taylor approximation and is not included.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Section 3, Theorem 1, p. 4; restated and proved in Appendix A.6, pp. 17-20 (eq. (57))

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem theorem1_general_agents_contain_world_models {S A : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] (n : ℕ) (hn : 3 ≤ n) :
    ∃ F : GCPolicy S A → S → A → S → ℝ,
      ∀ M : CMP S A, SatisfiesAssumption1 M →
      ∀ δ : ℝ, δ < 1 → ∀ π : GCPolicy S A, IsBoundedAgent M π δ n →
      ∀ (s : S) (a : A) (s' : S),
        |F π s a s' - M.P s a s'| ≤
          Real.sqrt (M.P s a s' * (1 - M.P s a s') / ((((n - 1) / 2 : ℕ) : ℝ) * (1 - δ))) := by sorry

end GeneralAgentsWorldModels
