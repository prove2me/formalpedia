-- Prove2me | Theorems.Thm_KellyLossNetworks_Routing_feasible_of_reservations
-- name    : KellyLossNetworks.Routing.feasible_of_reservations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:11:09.436519+00:00
-- url     : https://prove2.me/theorems/7bd270eb-9c83-4988-8c33-f2711a8fbd48
-- title:
--   Proof of Thm 4.45, p. 359 — if every excess edge's reservations cover its excess and no spare edge is over-reserved, the loads are routable
-- statement:
--   Let $x\ge 0$ be loads on the edges of the complete graph on $K$ nodes, $C$ the capacity of every edge, $D>0$ a scale, and $r_{e,k}$ the reservations of the proof of Theorem 4.45,
--   $$
--   r_{e,k}=\frac{(x_e-C)^+(C-x_{ak})^+(C-x_{bk})^+}{(K-2)D}\qquad (e=\{a,b\},\ k\notin e).
--   $$
--   Suppose that
--
--   1. every edge $e$ with **excess flow**, $x_e>C$, has $\sum_k r_{e,k}\ge x_e-C$ (the capacity reserved through two-link alternatives copes with the excess); and
--   2. every edge $g$ with **excess capacity**, $x_g<C$, has total capacity reserved through it, $\sum_{(e,k):\,g \text{ on the route of } e\text{ via } k} r_{e,k}$, at most $C-x_g$.
--
--   Then the loads $x$ can be carried over direct and two-edge routes with no edge carrying more than $C$.
--
--   This is the deterministic half of the proof: the probability that the loads are not routable is at most the probability that one of the two conditions fails at some edge.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 359, §4.6, proof of Theorem 4.45 (the two failure events); cf. p. 357, proof of Theorem 4.40 ('This procedure will work provided …')

import Mathlib
import Definitions.Def_KellyLossNetworks_Routing_Model

open MeasureTheory Filter Topology

namespace KellyLossNetworks.Routing

open Classical in
/-- **The reservations suffice when they cope.** Let `x ≥ 0` be loads on the complete graph on `K`
nodes, `C` the edge capacity and `D > 0` the scale of the reservations. Suppose that every edge
`e` with excess flow (`x e > C`) has total reservation `∑ k, reserve C D x e k ≥ x e - C`, and
that every edge `g` with excess capacity (`x g < C`) has total capacity reserved through it,
`∑ e, ∑ k, [g on the route of e via k] reserve C D x e k`, at most `C - x g`. Then the loads
can be carried over direct and two-edge routes without exceeding any capacity.

Kelly, *Loss networks*, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
§4.6, proof of Theorem 4.45, p. 359 (the reservation scheme; the step "the procedure works
provided …" is stated explicitly in the proof of Theorem 4.40, p. 357, and used implicitly on
p. 359). -/
theorem feasible_of_reservations {K : ℕ} (C D : ℝ) (hD : 0 < D) (x : Edge K → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hexcess : ∀ e, C < x e → x e - C ≤ ∑ k, reserve C D x e k)
    (hspare : ∀ g, x g < C →
      ∑ e, ∑ k, (if OnDetour e k g then reserve C D x e k else 0) ≤ C - x g) :
    Feasible C x := by sorry

end KellyLossNetworks.Routing
