-- Prove2me | Theorems.Thm_MDPComplexity_AverageCost_follow_cycle
-- name    : MDPComplexity.AverageCost.follow_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:14.721384+00:00
-- url     : https://prove2.me/theorems/a2b7e442-4ecd-4682-a1ed-cf892935aa1a
-- title:
--   Following a reachable cycle forever attains its mean cost
-- statement:
--   Let $M$ be a finite stationary deterministic Markov decision process, $s_0$ an initial state and $C$ a simple cycle whose starting state can be reached from $s_0$. There is a state-and-time policy $\delta$ whose finite averages converge to the cycle mean:
--
--   $$\lim_{T\to\infty}\frac{1}{T}\sum_{t=0}^{T}c(s_t,\delta(s_t,t))=\frac{1}{|C|}\sum_{e\in C}c(e).$$
--
--   This is the attainment half of the paper's reduction of average-cost optimization to reachable cycles.
--
--   **Formalization Note** A cycle retains its decision arcs, including parallel arcs and loops. Its states are distinct; the initial finite walk can have repeated states. At $T=0$ the finite average is set to zero, with no effect on convergence.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3 The infinite horizon undiscounted case, proof of Theorem 3, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_Model

namespace MDPComplexity.AverageCost

open Filter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §3, p. 446: an infinite path which reaches a cycle and follows it forever
has limiting average cost equal to that cycle's mean. -/
theorem follow_cycle (M : DetMDP S) (s₀ : S) :
    ∀ C : M.Cycle, M.Reachable s₀ C.base →
      ∃ δ : M.Policy, Tendsto (M.average s₀ δ) atTop (nhds C.mean) := by sorry

end MDPComplexity.AverageCost
