-- Prove2me | Theorems.Thm_MaxPressure_ReversedLeontief_pressure_split_by_processor
-- name    : MaxPressure.ReversedLeontief.pressure_split_by_processor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:07:05.458066+00:00
-- url     : https://prove2.me/theorems/349e2290-cebb-4221-bcfb-635fa150896b
-- title:
--   Proof of Lemma 3, p. 208 — $j_k(a)\in\mathcal J(k)$ and $p(a,z)=\sum_k p(j_k(a),z)$ for $a\in\mathcal E$
-- statement:
--   Consider a reversed Leontief network satisfying the standing assumptions of §2 and an extreme allocation $a\in\mathcal E$. Let $j_k(a)$ be the activity processor $k$ works on under $a$ ($0$ if $k$ is idle). Then
--
--   1. $j_k(a)\in\mathcal J(k)$ for every processor $k$;
--   2. for every $z\in\mathbb R^I$,
--   $$p(a,z)=\sum_{k\in\mathcal K}p(j_k(a),z),$$
--   where $p(0,z)=0$.
--
--   The second identity is used in the converse direction of Lemma 3: it turns the comparison of total pressures into a comparison processor by processor.
--
--   **Formalization Note.** $z$ is arbitrary here (the page has the buffer level $Z(t)\ge0$); this is a disclosed strengthening.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 208, §8, proof of Lemma 3 (converse direction)

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

namespace MaxPressure.ReversedLeontief

/-- Proof of Lemma 3, p. 208: in a reversed Leontief network, for an extreme allocation `a`,
`j_k(a) ∈ 𝒥(k)` for every processor `k`, and `p(a, z) = ∑_k p(j_k(a), z)` for every `z`. -/
theorem pressure_split_by_processor {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ k, activityOf N a k ∈ procActs N k) ∧
    ∀ z : Fin I → ℝ, pressure N a z = ∑ k, actPressure' N (activityOf N a k) z := by sorry

end MaxPressure.ReversedLeontief
