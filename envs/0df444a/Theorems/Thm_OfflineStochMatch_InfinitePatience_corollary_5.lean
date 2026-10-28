-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_corollary_5
-- name    : OfflineStochMatch.InfinitePatience.corollary_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:00.763637+00:00
-- url     : https://prove2.me/theorems/b0265a9a-c356-4414-b76a-2f3099b3a8f9
-- title:
--   Corollary 5, p. 16 — with every patience ∞, Algorithm 1 probes each edge e with probability ≥ (∫₀¹e^{−2x}dx)y_e = ½(1 − e^{−2})y_e
-- statement:
--   Let $G=(V,E)$ be a finite graph in which every edge $e$ is active independently with probability $p_e\in[0,1]$ and every vertex has patience $t_v=\infty$. Let $(y_e)_{e\in E}$ be any feasible solution of LP (3), and run Algorithm 1 with the exponential attenuation function $\tilde a(z)=e^{-z/2}$ or the linear one $\tilde a(z)=1-z/2$ (Definition 4 with $\alpha=1/2$), with $a(e)=\tilde a(p_ey_e)$. Then every edge $e$ is probed with probability
--   $$\Pr[e\text{ is probed}]\ \ge\ \Bigl(\int_0^1e^{-2x}\,dx\Bigr)y_e=\frac12\bigl(1-e^{-2}\bigr)y_e\approx 0.432\,y_e .$$
--
--   The algorithm considers the edges in a uniformly random order, so this is a per-edge guarantee of a random-order rounding scheme for LP (3) without patience constraints. Combined with (4) it bounds the expected weight of the matching by $\tfrac12(1-e^{-2})\sum_e w_ep_ey_e$.
--
--   **Formalization Note.** The paper says "the effective attenuation functions from Definition 4 with $\alpha=1/2$"; its proof sentence names the linear and exponential functions, and the third function of Definition 4 is not effective, so the statement covers exactly those two. The closing claim that the algorithm is a 0.432-approximation and a 0.432-balanced random-order contention resolution scheme needs a model of all adaptive probing algorithms (Lemma 1, from Bansal et al.) and is not stated. The equality $\int_0^1e^{-2x}dx=\frac12(1-e^{-2})$ is included as a conjunct, as on the page.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 16, §3.3, Corollary 5

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- Corollary 5, p. 16: with every patience `∞`, for any feasible solution of LP (3), Algorithm 1 with
the exponential or the linear attenuation function with `α = 1/2` probes every edge `e` with
probability at least `(∫_0^1 e^{-2x} dx) y_e = ½(1 - e^{-2}) y_e`. -/
theorem corollary_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (ht : ∀ v, t v = ⊤) (hy : LPFeasible G p t y)
    (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) (e : E) :
    (∫ x in (0 : ℝ)..1, Real.exp (-2 * x)) = (1 - Real.exp (-2)) / 2 ∧
      (1 - Real.exp (-2)) / 2 * y e ≤ probProbed G p t y aT e := by sorry

end OfflineStochMatch.InfinitePatience
