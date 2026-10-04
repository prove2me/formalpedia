-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_theorem_2_1
-- name    : OnlineRandomization.Simulation.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:16:42.013863+00:00
-- url     : https://prove2.me/theorems/ecba8c0f-3e11-4546-b8cd-8d9e08b01b88
-- title:
--   Theorem 2.1 — randomization adds no power against adaptive off-line adversaries
-- statement:
--   Let $\alpha$ be an affine cost transformation. If a randomized online algorithm is $\alpha$-competitive against every bounded-depth adaptive off-line adversary, then some deterministic online algorithm is $\alpha$-competitive on every request string:
--
--   $$\exists G_{\rm rand}\;\forall Q,\ \mathbb E[c_G(Q)]\leq\mathbb E[\alpha(c_Q(G))]
--   \quad\Longrightarrow\quad\exists D\;\forall r,\ c_D(r)\leq\alpha(c(r)).$$
--
--   Thus randomization alone does not improve the guarantee against this adversary class.
--
--   **Formalization Note** The randomized algorithm is supplied as a hypothesis on an arbitrary coin probability space, equivalent to the left existential. Costs are real (P1), $A$ finite nonempty (P2), algorithms use request prefixes (P5), adversaries have finite depth (P6), and each answer event is measurable (P4). No monotonicity of $\alpha$ is assumed.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 9, Theorem 2.1

import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 9, Theorem 2.1. -/
theorem theorem_2_1 {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (hα : IsLinear α) (H : RandAlg R A Ω)
    (hH : IsCompetitiveOffline F α H) :
    ∃ D : DetAlg R A, IsCompetitive F α D := by sorry

end OnlineRandomization.Simulation
