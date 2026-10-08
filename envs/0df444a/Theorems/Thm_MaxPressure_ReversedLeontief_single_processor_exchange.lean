-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_single_processor_exchange
-- name    : MaxPressure.ReversedLeontief.single_processor_exchange
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:07:14.063332+00:00
-- url     : https://prove2.me/theorems/e45f7347-c2b6-460f-b03d-6fa55a024eeb
-- title:
--   Proof of Lemma 3, p. 208 — the exchange $\tilde a=a-e_{j_k(a)}+e_j$ is extreme
-- statement:
--   Consider a reversed Leontief network satisfying the standing assumptions of §2, an extreme allocation $a\in\mathcal E$, a processor $k$ and a possible activity $j\in\mathcal J(k)$. Let $e_j$ be the $j$-th unit vector of $\mathbb R^J$, with $e_0=0$ for the idle Activity $0$, and let
--   $$\tilde a=a-e_{j_k(a)}+e_j.$$
--   Then $\tilde a\in\mathcal E$, and for every $z\in\mathbb R^I$
--   $$p(\tilde a,z)=p(a,z)-p(j_k(a),z)+p(j,z).$$
--
--   This single-processor exchange gives the forward direction of Lemma 3: if some processor could switch to an activity of strictly higher pressure, $a$ would not maximize the pressure.
--
--   **Formalization Note.** $z$ is arbitrary (the page has $Z(t)\ge0$), a disclosed strengthening; when $k$ is idle, $e_{j_k(a)}=e_0$ is the zero vector.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 208, §8, proof of Lemma 3 (forward direction)

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Proof of Lemma 3, p. 208: in a reversed Leontief network, for an extreme allocation `a`,
a processor `k` and `o ∈ 𝒥(k)`, the allocation `ã = a − e_{j_k(a)} + e_o` (with `e_0 = 0`
for the idle Activity 0) is extreme, and `p(ã, z) = p(a, z) − p(j_k(a), z) + p(o, z)`. -/
theorem single_processor_exchange {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) (k : Fin K)
    (o : Option (Fin J)) (ho : o ∈ procActs N k) :
    a - unitVec (activityOf N a k) + unitVec o ∈ extremeAllocs N ∧
    ∀ z : Fin I → ℝ, pressure N (a - unitVec (activityOf N a k) + unitVec o) z =
      pressure N a z - actPressure' N (activityOf N a k) z + actPressure' N o z := by sorry

end MaxPressure.ReversedLeontief
