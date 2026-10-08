-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_limit_weakly_stationary
-- name    : MPECRelax.ScholtesConv.limit_weakly_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:52:02.128115+00:00
-- url     : https://prove2.me/theorems/4b390281-ef91-4aa4-9bae-a120fdfd8711
-- title:
--   Proof of Theorem 3.1, pp. 10–11 — the limit x* is weakly stationary
-- statement:
--   Let the MPEC data $f,g,h,G,H$ be continuously differentiable, let $\{t_k\}\downarrow0$, let $x^k$ be a stationary (KKT) point of Scholtes' relaxed program $R^S(t_k)$ for every $k$, let $x^k\to x^*$, and let MPEC-MFCQ hold at $x^*$. Then $x^*$ is feasible for (1) and **weakly stationary**: there are $\lambda^*\in\mathbb R^m$, $\mu^*\in\mathbb R^p$, $\gamma^*,\nu^*\in\mathbb R^l$ with $\lambda^*\ge0$, $\lambda^*_ig_i(x^*)=0$, $\gamma^*_i=0$ ($i\in I_{+0}$), $\nu^*_i=0$ ($i\in I_{0+}$) and
--
--   $$0=\nabla f(x^*)+\sum_{i=1}^m\lambda^*_i\nabla g_i(x^*)+\sum_{i=1}^p\mu^*_i\nabla h_i(x^*)-\sum_{i=1}^l\gamma^*_i\nabla G_i(x^*)-\sum_{i=1}^l\nu^*_i\nabla H_i(x^*).$$
--
--   This is the first half of Theorem 3.1; the remaining step is the sign condition on $I_{00}$.
--
--   **Formalization Note** The paper states this inside the proof of Theorem 3.1, for multipliers obtained as limits of modified KKT multipliers of $R^S(t_k)$; the statement here asserts only the existence of weak-stationarity multipliers, with the same hypotheses as Theorem 3.1. "Stationary point" means KKT point including feasibility (p. 5); $\{t_k\}\downarrow0$ is $t_k>0$, nonincreasing, $t_k\to0$.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 10–11, proof of Theorem 3.1

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes

open Filter Topology

namespace MPECRelax.ScholtesConv

theorem limit_weakly_stationary {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).IsKKTPoint (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_MFCQ xs) :
    P.IsWeaklyStationary xs := by sorry

end MPECRelax.ScholtesConv
