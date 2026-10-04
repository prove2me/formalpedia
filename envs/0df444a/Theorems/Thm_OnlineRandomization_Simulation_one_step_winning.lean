-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_one_step_winning
-- name    : OnlineRandomization.Simulation.one_step_winning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:03.280072+00:00
-- url     : https://prove2.me/theorems/c03822b8-85d0-465c-a9cc-5d67acc636e3
-- title:
--   Proof of Theorem 2.1, p. 10 — corrected one-step winning characterization
-- statement:
--   For any equal-length request and answer strings $(r,a)$, a position is winning if it is immediately winning or the request player can choose one request $x$ such that every possible answer $y$ leads to a winning position:
--
--   $$\operatorname{Win}(r,a)\iff
--   f(r,a)>\alpha(c(r))\ \lor\
--   \exists x\in R\;\forall y\in A,\ \operatorname{Win}(r x,a y).$$
--
--   Finiteness of $A$ supplies one uniform bound on the remaining number of rounds.
--
--   **Formalization Note** The paper's printed equivalence omits the immediate-win case; that omission would make the reverse implication false at positions where the request player should stop. The Lean statement includes it. Costs are real and $A$ is finite nonempty (P1–P2); lists are oldest first (P5).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 10, §2, proof of Theorem 2.1, second paragraph

import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

/-- Manuscript p. 10, proof of Theorem 2.1, second paragraph. The printed
equivalence needs the immediate-win disjunct, since R may stop there. -/
theorem one_step_winning {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A)
    (hlen : r.length = a.length) :
    IsWinning F α r a ↔
      (α (F.opt r) < F.cost r a ∨
        ∃ x : R, ∀ y : A, IsWinning F α (r ++ [x]) (a ++ [y])) := by sorry

end OnlineRandomization.Simulation
