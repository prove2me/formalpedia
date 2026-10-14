-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_eq_4
-- name    : OfflineStochMatch.InfinitePatience.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:56.693442+00:00
-- url     : https://prove2.me/theorems/07e6d9e5-9313-4a11-8c34-8def3fc73d14
-- title:
--   Eq. (4), p. 9 — the expected matched weight of Algorithm 1 is Σ w_e p_e Pr[e free] Pr[Y_e = 1 ∩ A_e = 1] = Σ w_e p_e y_e a(e) Pr[e free]
-- statement:
--   Let $G=(V,E)$ be a graph with activeness probabilities $p_e\in[0,1]$, arbitrary patiences $t_v\in\mathbb N\cup\{\infty\}$ and a feasible solution $(y_e)$ of LP (3), and let $\tilde a$ map $[0,1]$ into $[0,1]$, with $a(e)=\tilde a(p_ey_e)$. Run Algorithm 1; an edge is *matched* when it is probed and active ($P_e=1$). Then for all real weights $(w_e)_{e\in E}$ the expected weight of the matching satisfies
--   $$\sum_{e\in E} w_e\Pr[e\text{ probed and }P_e=1]=\sum_{e\in E}w_ep_e\Pr[e\text{ is free}]\Pr[Y_e=1\cap A_e=1]=\sum_{e\in E}w_ep_ey_ea(e)\Pr[e\text{ is free}].$$
--
--   The identity reflects that the algorithm decides to probe $e$ before it learns $P_e$, and that "e is free" depends only on the edges processed before $e$. It reduces the expected weight of Algorithm 1 to the per-edge quantity $a(e)\Pr[e\text{ is free}]$, and $\Pr[e\text{ is probed}]=y_ea(e)\Pr[e\text{ is free}]$.
--
--   **Formalization Note.** The identity holds for every patience, so no patience hypothesis is assumed. Of LP (3) only $0\le y_e\le 1$ matters.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 9, §3.2, Eq. (4)

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- (4), p. 9: the expected weight of the matching produced by Algorithm 1 (an edge is matched when
it is probed and active) equals `∑_e w_e p_e Pr[e is free] Pr[Y_e = 1 ∩ A_e = 1]`, which equals
`∑_e w_e p_e y_e a(e) Pr[e is free]`, for any patience and any weights. -/
theorem eq_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y w : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : LPFeasible G p t y)
    (haT : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) :
    ∑ e, w e * prob p y aT (fun σ Y A P => IsProbed G t σ Y A P e ∧ P e = true)
        = ∑ e, w e * p e * probFree G p t y aT e *
            prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true) ∧
      ∑ e, w e * p e * probFree G p t y aT e *
            prob p y aT (fun _ Y A _ => Y e = true ∧ A e = true)
        = ∑ e, w e * p e * y e * aT (p e * y e) * probFree G p t y aT e := by sorry

end OfflineStochMatch.InfinitePatience
