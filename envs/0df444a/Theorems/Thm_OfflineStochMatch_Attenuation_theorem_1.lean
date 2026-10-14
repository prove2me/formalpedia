-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_theorem_1
-- name    : OfflineStochMatch.Attenuation.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:34.44312+00:00
-- url     : https://prove2.me/theorems/a1f58de4-590d-4e82-afb5-65e2aadcd5f9
-- title:
--   Theorem 1, p. 9 — with every patience ≥ 2, Algorithm 1 gives every edge a(e)·Pr[e is free] ≥ β*
-- statement:
--   Let $G = (V,E)$ be a finite graph (no loops, no parallel edges) in which each edge $e$ is active independently with probability $p_e \in [0,1]$ and each vertex $v$ has patience $t_v \in \{2, 3, \dots\} \cup \{\infty\}$, so that the minimum patience is at least $2$. Let $(y_f)_{f \in E}$ be any feasible solution of LP (3), and let $\tilde a$ be the exponential attenuation function $\tilde a(z) = e^{-z/2}$ or the linear one $\tilde a(z) = 1 - z/2$ (Definition 4 with $\alpha = 1/2$), with $a(e) = \tilde a(p_e y_e)$. When Algorithm 1 runs on $G$, every edge $e \in E$ satisfies
--   $$a(e) \cdot \Pr[e \text{ is free}] \;\ge\; \beta^* = \int_0^1 \left(e^{-2x} + x e^{-2x}\right)^2 dx \approx 0.38278. \tag{6}$$
--
--   Together with (4), which writes the expected weight of the matching as $\sum_e w_e p_e y_e\, a(e) \Pr[e \text{ is free}]$, and the LP upper bound of Bansal et al., this yields the paper's $0.382$-approximation for offline stochastic matching with patience at least $2$.
--
--   **Formalization Note**
--   1. The page says "$a$ is taken from Definition 3 where $\alpha = 1/2$ if the exponential or linear attenuation function is chosen". The parameter $\alpha$ appears only in Definition 4, and an arbitrary effective function cannot work (e.g. $e^{-10z}$ gives $a(e) < \beta^*$ when $p_e y_e = 1$), so the theorem is stated for the two functions named, with $\alpha = 1/2$. The third function of Definition 4 is not covered: it is not effective, and the paper's argument does not apply to it.
--   2. "Minimum patience 2" is $t_v \ge 2$ for every vertex, with $t_v = \infty$ allowed.
--   3. The paper's graph has edges $e = \{u,v\}$, i.e. no parallel edges; the platform graph type allows them, so injectivity of the endpoint map is a hypothesis.
--   4. $\Pr[e \text{ is free}]$ is computed from the run of Algorithm 1 over a uniformly random order and independent coins (see the Setting).
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 9, Theorem 1, Eq. (6) (β* from Eq. (5), p. 9)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem theorem_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, 2 ≤ t v) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    betaStar ≤ attProb aT p y e * probFree G p t y aT e := by sorry

end OfflineStochMatch.Attenuation
