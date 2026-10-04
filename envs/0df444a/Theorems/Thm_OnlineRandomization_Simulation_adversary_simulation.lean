-- Prove2me | Theorems.Thm_OnlineRandomization_Simulation_adversary_simulation
-- name    : OnlineRandomization.Simulation.adversary_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:16:51.490308+00:00
-- url     : https://prove2.me/theorems/c1121132-0ee0-4aff-965e-12ff7fd67190
-- title:
--   Proof of Theorem 2.2, p. 11 — simulate a fixed algorithm as an adaptive on-line adversary
-- statement:
--   Given an adaptive off-line request rule $Q$ and a fixed deterministic online algorithm $D$, there is an adaptive on-line adversary $S$ with the same request rule whose own answer string on every play against any deterministic algorithm $G$ equals the answers that $D$ would give to the resulting request string:
--
--   $$S_{\rm requests}=Q,\qquad b(G,S)=D(r(G,Q))\quad\text{for every }G.$$
--
--   This construction lets the adaptive on-line guarantee compare $G$ to any fixed realization of a randomized benchmark.
--
--   **Formalization Note** The adversary's answer rule can depend on prior answers through $Q$; the manuscript's parenthetical claim that its component functions are constants is imprecise. Lists are oldest first (P5), and the adversary has a uniform finite depth (P6).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 11, §2, proof of Theorem 2.2, second paragraph

import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- Manuscript p. 11, proof of Theorem 2.2: an adaptive online adversary
can answer its own requests using a fixed deterministic online algorithm. -/
theorem adversary_simulation {R A : Type*} (Q : OfflineAdv R A)
    (D : DetAlg R A) :
    ∃ S : OnlineAdv R A, S.toOfflineAdv = Q ∧
      ∀ G : DetAlg R A,
        onlineAnswers G S = D.answers (play G Q).1 := by sorry

end OnlineRandomization.Simulation
