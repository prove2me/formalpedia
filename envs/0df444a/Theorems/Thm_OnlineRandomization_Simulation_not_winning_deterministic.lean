-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_not_winning_deterministic
-- name    : OnlineRandomization.Simulation.not_winning_deterministic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:36:09.040918+00:00
-- url     : https://prove2.me/theorems/69fc7a7d-27d7-4649-a9a3-11ee75a62353
-- title:
--   Proof of Theorem 2.1, p. 10 — a nonwinning initial position yields an online strategy
-- statement:
--   If the request player cannot force an immediate cost violation from the empty position, then there is a deterministic online algorithm $D$ whose cost on every fixed request string stays below the transformed off-line optimum:
--
--   $$\neg\operatorname{Win}(\varnothing,\varnothing)\quad\Longrightarrow\quad
--   \exists D\;\forall r,\ c_D(r)\leq\alpha(c(r)).$$
--
--   This is the answer player's determinacy step in Theorem 2.1.
--
--   **Formalization Note** $D$ sees only each request prefix, never future requests (P5). The result includes the empty request string and uses finite nonempty $A$ (P2).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 10, §2, proof of Theorem 2.1, opening through final paragraph

import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

/-- Manuscript p. 10, proof of Theorem 2.1: if the request player cannot
force a bad finite play, the answer player has an online response strategy. -/
theorem not_winning_deterministic {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ)
    (h : ¬ IsWinning F α [] []) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by sorry

end OnlineRandomization.Simulation
