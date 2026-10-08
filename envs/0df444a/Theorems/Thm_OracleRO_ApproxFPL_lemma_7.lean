-- Prove2me | Theorems.Thm_OracleRO_ApproxFPL_lemma_7
-- name    : OracleRO.ApproxFPL.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:30:36.438567+00:00
-- url     : https://prove2.me/theorems/96f6f496-1d6c-4735-8e83-ad5b553cdec8
-- title:
--   Lemma 7 — being the approximate leader: $\sum_{t} M_\epsilon(f_{1:t})\cdot f_t \ge M_\epsilon(f_{1:T})\cdot f_{1:T} - \epsilon T$
-- statement:
--   Let $\mathcal K \subseteq \mathbb R^n$, let $\epsilon > 0$, and let $M_\epsilon$ be an $\epsilon$-approximate linear optimization procedure over $\mathcal K$: $M_\epsilon(g)\in\mathcal K$ and $g\cdot M_\epsilon(g) \ge g\cdot x - \epsilon$ for all $g\in\mathbb R^n$ and $x\in\mathcal K$. Write $f_{1:t} = \sum_{\tau=1}^t f_\tau$. Then for any vectors $f_1, \ldots, f_T \in \mathbb R^n$,
--   $$
--   \sum_{t=1}^T M_\epsilon(f_{1:t}) \cdot f_t \;\ge\; M_\epsilon(f_{1:T}) \cdot f_{1:T} - \epsilon T .
--   $$
--
--   The left side is the total reward of the hypothetical "be the leader" strategy that, at round $t$, already knows $f_t$ and plays the approximate leader for $f_{1:t}$. The lemma says this strategy loses at most $\epsilon$ per round against its own final choice. It is the first step of the Kalai–Vempala analysis, adapted to an approximate oracle.
--
--   **Formalization Note** The statement is for every $T \ge 0$; at $T = 0$ both sides vanish.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 12, Lemma 7

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- Lemma 7 (Ben-Tal, Hazan, Koren, Mannor, arXiv:1402.6361v1, p. 12): being the approximate
leader. For an `ε`-approximate linear optimization procedure `M` over `K` and any reward vectors
`f_1, …, f_T`,
`∑_{t=1}^T M(f_{1:t}) · f_t ≥ M(f_{1:T}) · f_{1:T} - εT`. -/
theorem lemma_7 {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) :
    M (prefixSum f T) ⬝ᵥ prefixSum f T - ε * T ≤
      ∑ t ∈ Finset.Icc 1 T, M (prefixSum f t) ⬝ᵥ f t := by sorry

end OracleRO.ApproxFPL
