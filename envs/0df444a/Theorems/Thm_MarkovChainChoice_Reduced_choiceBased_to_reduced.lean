-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_choiceBased_to_reduced
-- name    : MarkovChainChoice.Reduced.choiceBased_to_reduced
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:34:59.23538+00:00
-- url     : https://prove2.me/theorems/5b5e809a-bd70-4e56-9357-7a5f7ab5f3ec
-- title:
--   Proof of Theorem 7, p. 1332 — a (Choice Based) solution u gives the (Reduced) solution x̃_j = Σ_S P_{j,S} u_S, z̃_j = Σ_S R_{j,S} u_S with the same objective
-- statement:
--   Consider the network revenue management problem with $m$ resources of capacities $c_q$, a horizon of $T$ periods, revenues $r_j$ and consumptions $a_{q,j}$, under a Markov chain choice model. Let $u$ be any feasible solution of the (Choice Based) linear program, i.e. $u_S\ge 0$ for all $S\subseteq N$, $\sum_{S\subseteq N}\sum_{j\in N}T a_{q,j}P_{j,S}u_S\le c_q$ for all $q$, and $\sum_{S\subseteq N}u_S = 1$. Define
--   $$\tilde x_j = \sum_{S\subseteq N}P_{j,S}\,u_S,\qquad \tilde z_j = \sum_{S\subseteq N}R_{j,S}\,u_S\qquad (j\in N).$$
--   Then $(\tilde x,\tilde z)$ is a feasible solution of the (Reduced) linear program, and
--   $$\sum_{j\in N}T r_j\tilde x_j = \sum_{S\subseteq N}\sum_{j\in N}T r_j P_{j,S}u_S .$$
--
--   This shows that the optimal value of (Reduced) is at least that of (Choice Based).
--
--   **Formalization Note** The paper applies this construction to an optimal solution $\tilde u$ of (Choice Based); the argument uses only feasibility of $\tilde u$, so the statement is made for every feasible $u$. The equality of objective values is the identity used in the last sentence of the paragraph.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1332, proof of Theorem 7, left column, first paragraph

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model
import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms

namespace MarkovChainChoice.Reduced

theorem choiceBased_to_reduced {m n : ℕ} (M : Model n) (T : ℕ) (a : Fin m → Fin n → ℝ)
    (c : Fin m → ℝ) (r : Fin n → ℝ) (u : Finset (Fin n) → ℝ)
    (hu : ChoiceBasedFeasible M T a c u) :
    ReducedFeasible M T a c
        (fun j => ∑ S, purchase M S j * u S, fun j => ∑ S, visitNot M S j * u S) ∧
      reducedObjective T r
          (fun j => ∑ S, purchase M S j * u S, fun j => ∑ S, visitNot M S j * u S) =
        choiceBasedObjective M T r u := by sorry

end MarkovChainChoice.Reduced
