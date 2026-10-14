-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_eq_7
-- name    : OfflineStochMatch.InfinitePatience.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:56.807267+00:00
-- url     : https://prove2.me/theorems/76992389-498a-4547-b06d-0f75c3361c93
-- title:
--   Eq. (7), p. 10 — a safe edge is free, so a(e)·Pr[e is free] ≥ ã(p_e y_e)·Pr[e is safe]
-- statement:
--   Let $G=(V,E)$ be a graph with activeness probabilities $p_e\in[0,1]$, patiences $t_v\in\mathbb N\cup\{\infty\}$, a feasible solution $(y_e)$ of LP (3), and an attenuation function $\tilde a$ mapping $[0,1]$ into $[0,1]$. For every edge $e$, under Algorithm 1,
--   $$a(e)\cdot\Pr[e\text{ is free}]\ \ge\ \tilde a(p_ey_e)\Pr[e\text{ is safe}],\qquad a(e)=\tilde a(p_ey_e).$$
--
--   Here $e=\{u,v\}$ is *safe* when, before $e$ is processed, at most $t_r-1$ probes were made at each endpoint $r$, and no edge $f\ne e$ sharing an endpoint with $e$ and processed earlier has $A_f=P_f=Y_f=1$. Being safe implies being free, which gives the inequality. The safe event depends only on the edges at the endpoints of $e$, which is what makes its probability computable.
--
--   **Formalization Note.** The page's $X_f$ is $Y_f$ (no $X$ is defined in the paper).
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 10, Eq. (7) (safe event defined on p. 9)

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- (7), p. 10: a safe edge is free, so `a(e) · Pr[e is free] ≥ ã(p_e y_e) Pr[e is safe]`. -/
theorem eq_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : LPFeasible G p t y)
    (haT : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    aT (p e * y e) * probSafe G p t y aT e ≤ aT (p e * y e) * probFree G p t y aT e := by sorry

end OfflineStochMatch.InfinitePatience
