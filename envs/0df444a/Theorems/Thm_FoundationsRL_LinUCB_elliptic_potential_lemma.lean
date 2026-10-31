-- Prove2me | Theorems.Thm_FoundationsRL_LinUCB_elliptic_potential_lemma
-- name    : FoundationsRL.LinUCB.elliptic_potential_lemma
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:19:53.831293+00:00
-- url     : https://prove2.me/theorems/aaaf7773-d27f-459f-a850-affc22c6ee77
-- title:
--   Lemma 11 — elliptic potential lemma
-- statement:
--   Let $a_1,\dots,a_T\in\mathbb R^d$ satisfy $\|a_t\|\le1$ for all $t$, and let $V_t=I+\sum_{s\le t}a_sa_s^{\top}$. Then
--
--   $$
--   \sum_{t=1}^T\|a_t\|_{V_{t-1}^{-1}}^2\le2d\log(1+T/d).
--   $$
--
--   As more information accumulates in a direction, the matrix $V_t$ grows there and the corresponding width shrinks. Applied to the features played by LinUCB, this bounds the sum of squared confidence widths and yields the regret bound.
--
--   Differences from the source:
--   - encoding: rounds $1,\dots,T$ and $V_{t-1}$ → rounds $t<T$ and $I+\sum_{s<t}a_sa_s^{\top}$; reason: Lean indexes rounds from $0$.
--   - encoding: $\mathbb R^d$ → `Fin d → ℝ` with $0<d$; reason: the bound divides by $d$, and the book's ambient space has $d\ge1$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 11, Eq. (3.28), p. 45

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_ellipNormSq

open Matrix

namespace FoundationsRL.LinUCB

/-- Lemma 11, the elliptic potential lemma (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.28), p. 45): if `∥a_t∥ ≤ 1` for all `t` and
`V_t = I + ∑_{s≤t} a_s a_sᵀ`, then `∑_{t=1}^T ∥a_t∥²_{V_{t−1}⁻¹} ≤ 2d log(1 + T/d)`.

Lean's index `t < T` is the book's `t + 1`, so `V_{t−1}` of the book is
`1 + ∑ s ∈ range t, a s (a s)ᵀ` of Lean's round `t`. -/
theorem elliptic_potential_lemma {d : ℕ} (hd : 0 < d) (T : ℕ) (a : ℕ → Fin d → ℝ)
    (ha : ∀ t < T, a t ⬝ᵥ a t ≤ 1) :
    ∑ t ∈ Finset.range T,
        ellipNormSq (1 + ∑ s ∈ Finset.range t, vecMulVec (a s) (a s))⁻¹ (a t) ≤
      2 * d * Real.log (1 + T / d) := by sorry

end FoundationsRL.LinUCB
