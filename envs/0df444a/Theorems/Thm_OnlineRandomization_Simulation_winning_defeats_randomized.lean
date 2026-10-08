-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_winning_defeats_randomized
-- name    : OnlineRandomization.Simulation.winning_defeats_randomized
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:35:43.55498+00:00
-- url     : https://prove2.me/theorems/d2e27a6e-6264-4099-b02e-aa8d8241f780
-- title:
--   Proof of Theorem 2.1, pp. 9–10 — pointwise defeat survives expectation
-- statement:
--   Suppose one bounded-depth adaptive off-line adversary $Q$ defeats every deterministic online algorithm $D$ strictly. For every randomized online algorithm $G$ distributed over such algorithms, its expected cost is still strictly larger than the expected transformed adversary cost:
--
--   $$\forall D,\ c_D(Q)>\alpha(c_Q(D))\quad\Longrightarrow\quad
--   \mathbb E[c_G(Q)]>\mathbb E[\alpha(c_Q(G))].$$
--
--   This is the probabilistic step in the randomization-removal theorem.
--
--   **Formalization Note** The answer set is finite nonempty and the adversary has a uniform finite depth, so each play cost takes finitely many values and is integrable (P1–P2, P4, P6). The cost transform is inside the expectation, as on manuscript p. 9.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 9–10, §2, proof of Theorem 2.1, final and opening paragraphs

import Definitions.Def_OnlineRandomization_Simulation_Winning

namespace OnlineRandomization.Simulation

open MeasureTheory

/-- Manuscript pp. 9–10, proof of Theorem 2.1: strict pointwise defeat
persists under expectation because the adversary has finite depth and A is finite. -/
theorem winning_defeats_randomized {R A Ω : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace Ω] (F : Game R A) (α : ℝ → ℝ)
    (Q : OfflineAdv R A)
    (hQ : ∀ G : DetAlg R A,
      α (F.opt (play G Q).1) < F.cost (play G Q).1 (play G Q).2)
    (H : RandAlg R A Ω) :
    (∫ ω, α (F.opt (play (H.alg ω) Q).1) ∂H.μ) <
      (∫ ω, F.cost (play (H.alg ω) Q).1 (play (H.alg ω) Q).2 ∂H.μ) := by sorry

end OnlineRandomization.Simulation
