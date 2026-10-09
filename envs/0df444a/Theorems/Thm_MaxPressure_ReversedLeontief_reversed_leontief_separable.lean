-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_reversed_leontief_separable
-- name    : MaxPressure.ReversedLeontief.reversed_leontief_separable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:07:18.15845+00:00
-- url     : https://prove2.me/theorems/712cc8f8-0513-4e81-a1ba-0396e7cb5229
-- title:
--   Lemma 3, p. 208 — in a reversed Leontief network maximum pressure separates by processor
-- statement:
--   Consider a reversed Leontief network satisfying the standing assumptions of §2, a buffer-level vector $z\in\mathbb R^I_+$ and an extreme allocation $a\in\mathcal E$. For each processor $k$ let $j_k(a)$ be the activity $k$ works on under $a$ ($0$ if idle), $\mathcal J(k)$ the set (60) of possible activities of $k$, and $p(j,z)=\sum_{i}R_{ij}z_i$ the activity pressure, $p(0,z)=0$. Then
--   $$p(a,z)=\max_{a'\in\mathcal E}p(a',z)\quad\Longleftrightarrow\quad j_k(a)\in\operatorname*{arg\,max}_{j\in\mathcal J(k)}p(j,z)\ \text{ for all } k\in\mathcal K.$$
--
--   A maximum pressure policy in a reversed Leontief network is therefore a separable policy: each processor chooses, among its own possible activities, one of largest activity pressure, independently of the other processors. The paper uses this to show that nonpreemptive maximum pressure policies are throughput optimal in reversed Leontief networks (Theorem 9).
--
--   **Formalization Note.** "$p(a,z)=\max_{a'\in\mathcal E}p(a',z)$" is stated as $p(a',z)\le p(a,z)$ for every $a'\in\mathcal E$ (no supremum and no junk value; $a\in\mathcal E$ is a hypothesis, so the maximum is attained). The argmax condition is stated as $p(j,z)\le p(j_k(a),z)$ for every $j\in\mathcal J(k)$. The idle Activity $0$ is `none`.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 208, §8, Lemma 3

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Lemma 3, p. 208: in a reversed Leontief network, for any allocation `a ∈ ℰ` and buffer
level `z ≥ 0`, `p(a, z) = max_{a' ∈ ℰ} p(a', z)` if and only if
`j_k(a) ∈ argmax_{j ∈ 𝒥(k)} p(j, z)` for every processor `k`. -/
theorem reversed_leontief_separable {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ↔
      ∀ k, ∀ o ∈ procActs N k, actPressure' N o z ≤ actPressure' N (activityOf N a k) z := by sorry

end MaxPressure.ReversedLeontief
