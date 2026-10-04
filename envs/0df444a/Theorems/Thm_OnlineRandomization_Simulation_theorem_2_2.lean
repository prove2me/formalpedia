-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_theorem_2_2
-- name    : OnlineRandomization.Simulation.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:17:06.271478+00:00
-- url     : https://prove2.me/theorems/272f8134-02d0-4a04-bb0c-a4ab335da6d7
-- title:
--   Theorem 2.2 — composition of adaptive on-line and oblivious guarantees
-- statement:
--   Let $\alpha$ and $\beta$ be affine cost transformations. Suppose a randomized algorithm $G$ is $\alpha$-competitive against every adaptive on-line adversary, and another randomized algorithm $H$ is $\beta$-competitive against every oblivious adversary. Then $G$ is $\alpha\circ\beta$-competitive against every adaptive off-line adversary:
--
--   $$\mathbb E[c_G(Q)]\leq\mathbb E[(\alpha\circ\beta)(c_Q(G))]\quad\text{for every }Q.$$
--
--   This links the three adversary models at the paper's exact composed cost transformation.
--
--   **Formalization Note** Applying $\alpha$ to an inequality on manuscript p. 11 requires it to be monotone; the Lean statement includes this implicit condition (P3). Costs are real and $A$ finite nonempty (P1–P2); the two algorithms have independently measurable coin spaces, with finite-range play costs (P4); lists and adversaries follow P5–P6. The coin types are Lean types at the declaration's universe level.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 10, Theorem 2.2

import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 10, Theorem 2.2. -/
theorem theorem_2_2 {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α) (hβ : IsLinear β)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    IsCompetitiveOffline F (α ∘ β) G := by sorry

end OnlineRandomization.Simulation
