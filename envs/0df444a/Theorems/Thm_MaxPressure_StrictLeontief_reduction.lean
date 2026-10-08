-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_reduction
-- name    : MaxPressure.StrictLeontief.reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:56:20.538759+00:00
-- url     : https://prove2.me/theorems/db00da1f-b51b-4dba-8d43-17bab3ecb1ff
-- title:
--   §6.1, proof of Theorem 6, p. 204 — it suffices to find a maximizing extreme allocation vanishing on J₀
-- statement:
--   Consider a strict Leontief network satisfying the standing assumptions of §2, a buffer-level vector $z\in\mathbb R^I_+$, and the set $\mathcal J_0$ of service activities $j$ with $z_{i(j)}=0$. If there is an allocation
--   $$a^*\in\arg\max_{a\in\mathcal E}z'Ra\quad\text{with}\quad a^*_j=0\ \text{ for all } j\in\mathcal J_0,$$
--   then there is an extreme allocation $a^*\in\mathcal E$ with $p(a^*,z)=\max_{a\in\mathcal E}p(a,z)$ such that $z_i>0$ for every constituent buffer $i$ of $a^*$, which is the conclusion of Assumption 1 at $z$.
--
--   This is the reduction with which the proof of Theorem 6 begins.
--
--   **Formalization Note** "argmax" and "maximum" are stated in domination form over $\mathcal E$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 204, §6.1, proof of Theorem 6, sentences 4–5

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204 ("It is sufficient to show"): for `z ∈ ℝ^I_+`, if some
extreme allocation maximizes `p(·, z)` over `ℰ` and vanishes on `𝒥₀`, then some extreme
allocation maximizes `p(·, z)` over `ℰ` and every constituent buffer of it has a positive
level, which is the conclusion of Assumption 1 at `z`. -/
theorem reduction {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (h : ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i := by sorry

end MaxPressure.StrictLeontief
