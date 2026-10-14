-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_eq_7
-- name    : OfflineStochMatch.Attenuation.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:16.092703+00:00
-- url     : https://prove2.me/theorems/bb6f428a-be79-4c33-9476-3872db039695
-- title:
--   Eq. (7), p. 10 — a(e)·Pr[e is free] ≥ ã(p_e y_e)·Pr[e is safe]
-- statement:
--   Let Algorithm 1 run on a finite graph $G = (V,E)$ with activeness probabilities $p_f \in [0,1]$, patience values $t_v \in \{1,2,\dots\}\cup\{\infty\}$, probing probabilities $y_f \in [0,1]$, and an attenuation function $\tilde a$ mapping $[0,1]$ into $[0,1]$, so that edge $f$ has attenuation $a(f) = \tilde a(p_f y_f)$. Then for every edge $e$,
--   $$a(e) \cdot \Pr[e \text{ is free}] \;\ge\; \tilde a(p_e y_e)\, \Pr[e \text{ is safe}].$$
--
--   The inequality holds because a safe edge is free. It reduces the goal theorem to a lower bound on the probability of the event *safe*, which depends only on the edges incident to the endpoints of $e$.
--
--   **Formalization Note** Since $a(e) = \tilde a(p_e y_e)$, both sides carry the same factor. LP feasibility is not needed for this step and is not assumed; only $y_f \in [0,1]$ (3c) is.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 10, Eq. (7) (safe event defined on p. 9)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem eq_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1)
    (haT : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    aT (p e * y e) * probSafe G p t y aT e ≤ aT (p e * y e) * probFree G p t y aT e := by sorry

end OfflineStochMatch.Attenuation
