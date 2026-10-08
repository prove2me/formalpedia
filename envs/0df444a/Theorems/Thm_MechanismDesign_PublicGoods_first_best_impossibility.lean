-- Prove2me | Theorems.Thm_MechanismDesign_PublicGoods_first_best_impossibility
-- name    : MechanismDesign.PublicGoods.first_best_impossibility
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:20:19.920912+00:00
-- url     : https://prove2.me/theorems/82b7f1a6-3d20-4f60-8d09-b45eca81ce5e
-- title:
--   Proposition 3.7 — an IC and IR first best public goods mechanism exists iff $N\underline\theta \ge c$ or $N\bar\theta \le c$
-- statement:
--   Consider the public goods model of Börgers §3.3: $N \ge 2$ agents with independent types $\theta_i \in [\underline\theta,\bar\theta]$, $0 \le \underline\theta < \bar\theta$, drawn from densities $f_i > 0$, and a public good of cost $c>0$. A direct mechanism is **first best** if its decision rule is
--   $$q^*(\theta) = \begin{cases} 1 & \text{if } \sum_{i\in I}\theta_i \ge c,\\ 0 & \text{otherwise,}\end{cases}$$
--   and its transfers satisfy $\sum_{i\in I} t_i(\theta) = c$ if $q^*(\theta) = 1$ and $\sum_{i\in I} t_i(\theta) = 0$ otherwise, for every $\theta \in \Theta$.
--
--   **Proposition 3.7.** An incentive-compatible and individually rational first best mechanism exists if and only if either $N\underline\theta \ge c$ or $N\bar\theta \le c$.
--
--   In the two cases of the condition, production is efficient for all type vectors or for none. In every other case the proposition is an impossibility result: efficient provision of the public good, financed exactly by the agents' voluntary payments, cannot be made incentive compatible. It is the public goods counterpart of the Myerson–Satterthwaite theorem.
--
--   **Formalization Note** "First best" requires both the decision rule $q^*$ and exact budget balance $\sum_i t_i = c\,q^*$ in every state; requiring only the decision rule would make the pivot mechanism a witness in every case. The mechanisms range over the class `IsDirect`, which adds the measurability and integrability the book leaves implicit.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.50, Proposition 3.7 ((3.21)–(3.22))

import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.7 (p.50): an incentive-compatible and individually rational first best
mechanism exists if and only if either `N θ̲ ≥ c` or `N θ̄ ≤ c`. "First best" is (3.21)–(3.22):
decision rule `q*` and transfers summing to exactly `c q*(θ)` in every state `θ ∈ Θ`. -/
theorem first_best_impossibility {N : ℕ} (S : Setting N) :
    (∃ M : DirectMechanism N, M.IsDirect S ∧ M.IsFirstBest S ∧ M.IsIC S ∧ M.IsIR S) ↔
      (S.c ≤ (N : ℝ) * S.θlo ∨ (N : ℝ) * S.θhi ≤ S.c) := by sorry

end MechanismDesign.PublicGoods
