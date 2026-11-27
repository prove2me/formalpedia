-- Prove2me | Theorems.Thm_LefebvreVariations_stable_roommates_four_agents_unsolvable
-- name    : LefebvreVariations.stable_roommates_four_agents_unsolvable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:20:05.869092+00:00
-- url     : https://prove2.me/theorems/a52ee4b6-bdbd-5ddc-9fbb-24c275ed5f17
-- title:
--   Lefebvre's variations, No. 255 — on a theme by Gale and Shapley: four roommates can have rankings with no stable pairing
-- statement:
--   Four agents each rank the other three strictly. A pairing is a fixed-point-free involution $\mu$ of the four agents, and agents $i\neq j$ with $j\neq\mu(i)$ form a blocking pair if $i$ ranks $j$ above $\mu(i)$ and $j$ ranks $i$ above $\mu(j)$. There exist rankings $r$ for which every pairing has a blocking pair:
--   $$\exists r\ \ \forall \mu\ \ \exists\, i\neq j:\ r_i(j)<r_i(\mu(i))\ \wedge\ r_j(i)<r_j(\mu(j)).$$
--
--   Unlike the marriage problem, the stable roommates problem can have no solution. Four agents is the smallest even size where this happens, since for two agents there is only one pairing. A classical instance has three agents who prefer each other in a cycle and a fourth agent whom everybody ranks last.
--
--   **Formalization Note** The ranking is \texttt{r : Fin 4 $\to$ Fin 4 $\to$ $\mathbb N$} with \texttt{r i j} the rank of $j$ for $i$, required injective on the other agents (the entry \texttt{r i i} is unconstrained and unused). A pairing is \texttt{$\mu$ : Equiv.Perm (Fin 4)} with no fixed point and $\mu(\mu(i))=i$.
--
--   **Why this is a variation.** No open platform problem on stable roommates feasibility was found (the nearest, TwoMasterRoommates, is about weakly stable matchings with ties). This is the smallest instance of the classical fact that stable roommates can be unsolvable, the starting point of the problem of deciding solvability (Irving's algorithm). No formal link to a platform parent is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. Gale and L. S. Shapley, "College admissions and the stability of marriage", Amer. Math. Monthly 69 (1962), 9-15: the roommates example with no stable matching (cited from memory). R. W. Irving, "An efficient algorithm for the stable roommates problem", J. Algorithms 6 (1985) (cited from memory). The instance 1: 2>3>4, 2: 3>1>4, 3: 1>2>4, 4: 1>2>3 was checked here by enumeration of the three pairings.

import Mathlib

namespace LefebvreVariations

/-- Four roommates can have no stable pairing. `r i j` is agent `i`'s rank of agent `j` (lower =
preferred), injective on the other agents. A pairing is a fixed-point-free involution `μ`, and a
pair `i, j` blocks it if each ranks the other strictly above their current partner. There are
rankings of four agents for which every pairing has a blocking pair. Source: Gale and Shapley,
*College admissions and the stability of marriage*, Amer. Math. Monthly 69 (1962), the roommates
example; Irving 1985 for the algorithm (cited from memory). -/
theorem stable_roommates_four_agents_unsolvable :
    ∃ r : Fin 4 → Fin 4 → ℕ,
      (∀ i j k, j ≠ i → k ≠ i → r i j = r i k → j = k) ∧
      ¬ ∃ μ : Equiv.Perm (Fin 4), (∀ i, μ i ≠ i) ∧ (∀ i, μ (μ i) = i) ∧
        ∀ i j, j ≠ i → j ≠ μ i → ¬ (r i j < r i (μ i) ∧ r j i < r j (μ j)) := by
  sorry

end LefebvreVariations
