-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_strict_leontief_eaa
-- name    : MaxPressure.StrictLeontief.strict_leontief_eaa
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:56:26.246461+00:00
-- url     : https://prove2.me/theorems/6fe2912b-0af5-4c22-8b43-f7c7190d7106
-- title:
--   Theorem 6, p. 204 — Assumption 1 (EAA) is satisfied for strict Leontief networks
-- statement:
--   **Theorem 6 (Dai–Lin 2005).** Let a stochastic processing network satisfy the standing assumptions of §2, have a nonempty allocation set $\mathcal A$, and be strict Leontief: every service activity processes exactly one buffer. Then Assumption 1 holds: for every $z\in\mathbb R^I_+$ there is an extreme allocation $a^*\in\mathcal E$ with
--   $$p(a^*,z)=\max_{a\in\mathcal E}p(a,z)$$
--   such that $z_i>0$ for every constituent buffer $i$ of $a^*$.
--
--   Combined with Theorem 2, it shows that maximum pressure policies are throughput optimal in every strict Leontief network, a class that includes networks of data switches.
--
--   **Formalization Note** Nonemptiness of $\mathcal A$ is an explicit hypothesis. The paper presupposes it, and it does not follow from the standing assumptions: a network with three input processors and two input activities, needing processors $\{1,2\}$ and $\{2,3\}$, has $\mathcal A=\emptyset$, is vacuously strict Leontief, and violates Assumption 1. Constituent buffers are internal buffers only.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 204, Theorem 6

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Theorem 6, p. 204: Assumption 1 (EAA) is satisfied for strict Leontief networks. -/
theorem strict_leontief_eaa {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hA : (allocSet N).Nonempty) (hSL : IsStrictLeontief N) : EAA N := by sorry

end MaxPressure.StrictLeontief
