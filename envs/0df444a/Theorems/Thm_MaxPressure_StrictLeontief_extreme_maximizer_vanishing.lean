-- Prove2me | Theorems.Thm_MaxPressure_StrictLeontief_extreme_maximizer_vanishing
-- name    : MaxPressure.StrictLeontief.extreme_maximizer_vanishing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:56:11.661859+00:00
-- url     : https://prove2.me/theorems/94efd397-5e78-4ebb-857d-84a9eaf13922
-- title:
--   §6.1, proof of Theorem 6, p. 204 — an extreme allocation in a decomposition of ã is a maximizer vanishing on J₀
-- statement:
--   Consider a strict Leontief network satisfying the standing assumptions of §2, a buffer-level vector $z\in\mathbb R^I_+$, and the set $\mathcal J_0$ of service activities $j$ with $z_{i(j)}=0$. Suppose $\tilde a\in\mathcal A$ satisfies
--   $$z'R\tilde a=\max_{a\in\mathcal A}z'Ra\qquad\text{and}\qquad \tilde a_j=0\ \text{ for all } j\in\mathcal J_0.$$
--   Then there is an extreme allocation $a^*\in\mathcal E$ with $z'Ra^*=\max_{a\in\mathcal A}z'Ra$ and $a^*_j=0$ for all $j\in\mathcal J_0$.
--
--   In the paper, $a^*$ is one of the extreme allocations of which $\tilde a$ is a convex combination. This step turns the maximizer produced by truncation back into an extreme allocation, as Assumption 1 requires.
--
--   **Formalization Note** "Maximum" is stated in domination form over $\mathcal A$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 204, §6.1, proof of Theorem 6, last three sentences

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network

namespace MaxPressure.StrictLeontief

/-- Proof of Theorem 6, p. 204: if `ã ∈ 𝒜` maximizes `p(·, z)` over `𝒜` and vanishes on
`𝒥₀`, then some extreme allocation `a* ∈ ℰ` (one of the extreme allocations of which `ã`
is a convex combination) maximizes `p(·, z)` over `𝒜` and vanishes on `𝒥₀`. -/
theorem extreme_maximizer_vanishing {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (at' : Fin J → ℝ) (hat : at' ∈ allocSet N)
    (hmax : ∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N at' z)
    (hvan : ∀ j ∈ J0 N z, at' j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ allocSet N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0 := by sorry

end MaxPressure.StrictLeontief
