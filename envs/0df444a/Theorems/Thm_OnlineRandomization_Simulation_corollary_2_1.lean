-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_corollary_2_1
-- name    : OnlineRandomization.Simulation.corollary_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:17:26.158115+00:00
-- url     : https://prove2.me/theorems/faed7b42-4e54-4d76-9952-5d5b1098acc6
-- title:
--   Corollary 2.1 — deterministic $\alpha\circ\beta$ competitiveness
-- statement:
--   Let $\alpha$ and $\beta$ be affine cost transformations. If a randomized online algorithm is $\alpha$-competitive against every adaptive on-line adversary and another randomized online algorithm is $\beta$-competitive against every oblivious adversary, then a deterministic online algorithm has the composed guarantee:
--
--   $$\exists D\;\forall r,\qquad c_D(r)\leq(\alpha\circ\beta)(c(r)).$$
--
--   The corollary is the paper's general derandomization conclusion for request-answer games.
--
--   **Formalization Note** $\alpha$ is assumed monotone because the source's proof of Theorem 2.2 applies it to an inequality (P3). Costs are real, $A$ finite nonempty, each randomized algorithm has a measurable coin probability space, request and answer lists are oldest first, and adaptive adversaries have finite depth (P1–P2, P4–P6). The coin types are Lean types at the declaration's universe level.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 13, Corollary 2.1

import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 13, Corollary 2.1. -/
theorem corollary_2_1 {R A Ω Ω' : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (F : Game R A) (α β : ℝ → ℝ)
    (hα : IsLinear α) (hαmono : Monotone α) (hβ : IsLinear β)
    (G : RandAlg R A Ω) (H : RandAlg R A Ω')
    (hG : IsCompetitiveOnline F α G)
    (hH : IsCompetitiveObl F β H) :
    ∃ D : DetAlg R A, IsCompetitive F (α ∘ β) D := by sorry

end OnlineRandomization.Simulation
