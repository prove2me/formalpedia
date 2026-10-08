-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_2
-- name    : JSQHalfinWhitt.Tightness.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:59.607146+00:00
-- url     : https://prove2.me/theorems/c7cd87e8-533e-4783-b966-9ee964eeb806
-- title:
--   Lemma 2 — $\mathbb EQ_1 = n\lambda$ and $\mathbb EQ_i = n\lambda\,\mathbb P(Q_1 = \dots = Q_{i-1} = n)$
-- statement:
--   Consider the join-the-shortest-queue chain with $n \ge 1$ servers and $\lambda \in (0,1)$, and let $Q = (Q_1, Q_2, \dots)$ have a stationary distribution of the chain, where $Q_i$ is the number of servers with at least $i$ customers. Then
--   $$\mathbb E Q_1 = n\lambda, \tag{3.2}$$
--   $$\mathbb E Q_i = n\lambda\, \mathbb P(Q_1 = \dots = Q_{i-1} = n),\qquad i > 1. \tag{3.3}$$
--
--   In particular $n - \mathbb E Q_1 = n(1-\lambda)$, so in the Halfin–Whitt regime $\sqrt n\,\mathbb E|X_1| = \beta$, which is the $i = 1$ case of (2.2).
--
--   **Formalization Note** Lean indices are 0-based: `q.1 0` is $Q_1$ and `q.1 i` ($i \ge 1$) is $Q_{i+1}$, so (3.3) for the paper's index $i+1$ reads $\mathbb E\,Q_{i+1} = n\lambda\,\mathbb P(Q_1 = \dots = Q_i = n)$. Expectations and probabilities are sums against $\pi$; all summands are bounded ($0 \le Q_i \le n$).
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 6, Lemma 2, (3.2)–(3.3)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

/-- Lemma 2 (Braverman, p. 6): for `n ≥ 1`, `λ ∈ (0, 1)` and every stationary distribution `π`
of the JSQ chain, `E Q_1 = nλ` (3.2) and `E Q_i = nλ P(Q_1 = … = Q_{i−1} = n)` for `i > 1` (3.3).
Lean indices are 0-based: `q.1 0` is `Q_1`, and `q.1 i` for `i ≥ 1` is `Q_{i+1}`. -/
theorem lemma_2 (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π) :
    expect π (fun q => (q.1 0 : ℝ)) = n * lam ∧
      ∀ i : ℕ, 1 ≤ i →
        expect π (fun q => (q.1 i : ℝ)) = n * lam * prob π (fun q => ∀ j, j < i → q.1 j = n) := by sorry

end JSQHalfinWhitt.Tightness
