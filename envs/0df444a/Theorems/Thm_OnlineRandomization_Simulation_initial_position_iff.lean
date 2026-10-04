-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_initial_position_iff
-- name    : OnlineRandomization.Simulation.initial_position_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:35:18.78499+00:00
-- url     : https://prove2.me/theorems/3c5e5087-cc0e-45e7-9033-0dc7511df627
-- title:
--   Proof of Theorem 2.1, p. 9 — the initial position and a defeating adversary
-- statement:
--   In a request-answer game with finite nonempty answer set, the empty position is winning for the request player exactly when one adaptive off-line adversary $Q$ defeats every deterministic online algorithm $D$:
--
--   $$\operatorname{Win}(\varnothing,\varnothing)\iff
--   \exists Q\;\forall D,\quad c_D(Q)>\alpha(c_Q(D)).$$
--
--   This connects the finite game with the adversary formulation of competitiveness.
--
--   **Formalization Note** The same $Q$ precedes every $D$ in the quantifiers. The adversary may stop at depth zero (P6); game costs are real and $A$ is finite nonempty (P1–P2).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 9, §2, proof of Theorem 2.1, first paragraph

import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

/-- Manuscript p. 9, proof of Theorem 2.1, first paragraph. -/
theorem initial_position_iff {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) :
    IsWinning F α [] [] ↔
      ∃ Q : OfflineAdv R A, ∀ G : DetAlg R A,
        α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2 := by sorry

end OnlineRandomization.Simulation
