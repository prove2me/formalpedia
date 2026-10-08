-- Prove2me | Theorems.Thm_KalaiVempala_Additive_eq_4
-- name    : KalaiVempala.Additive.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:53.087025+00:00
-- url     : https://prove2.me/theorems/ccda45bc-acd4-45b3-b7a9-bff36a5ce1e0
-- title:
--   (4), p. 299 — be the leader: Σ_{t≤T} M(s_{1:t})·s_t ≤ M(s_{1:T})·s_{1:T}
-- statement:
--   **Be the leader has no regret.** Let $\mathcal D \subset \mathbb R^n$ be a decision set and $M$ an argmin oracle for $\mathcal D$, so $M(x) \in \mathcal D$ minimises $d \cdot x$ over $d \in \mathcal D$. For a sequence of state vectors $s_1, s_2, \dots \in \mathbb R^n$ write $s_{1:t} = s_1 + \dots + s_t$. Then for every $T$,
--
--   $$\sum_{t=1}^{T} M(s_{1:t}) \cdot s_t \;\le\; M(s_{1:T}) \cdot s_{1:T}.$$
--
--   The left side is the cost of the hypothetical "be the leader" algorithm, which on day $t$ already uses the state $s_t$ it is about to pay; the right side is the cost of the best fixed decision in hindsight. This inequality is the starting point of the additive analysis of Follow the Perturbed Leader.
--
--   **Formalization Note** $T$ ranges over all natural numbers; at $T = 0$ both sides are $0$. The states are indexed from $1$ (`s 0` is unused) and $s_{1:t}$ is `prefixSum s t` from `OracleRO.ApproxFPL.FPL`. No bound on $\mathcal D$ or on the states is needed.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 299, display (4)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Additive

theorem eq_4 {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (s : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T := by sorry

end KalaiVempala.Additive
