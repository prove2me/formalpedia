-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_proposition_2
-- name    : MaintPOMDP.Frontier.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:03.506945+00:00
-- url     : https://prove2.me/theorems/128669ed-d5c1-4bb4-aa3d-35705ff5aa40
-- title:
--   Proposition 2, p. 17 — value iteration converges to a solution of the fixed-point equations (18)–(22)
-- statement:
--   Consider the maintenance model with obvious failures under its standing assumptions, with the action set $\{P,R\}$ or $\{P,I,R\}$. Run the dual value iteration (12)–(16) from zero terminal costs, in support-function form: the $n$-th iterate is a pair $(W_n,w_{F,n})$ with $W_n(\boldsymbol\pi)$ the expected optimal cost from an unnormalized belief $\boldsymbol\pi\ge0$ and $w_{F,n}$ the cost after a failure.
--
--   Then there are a function $W$ and a number $w_F$ such that $W_n(\boldsymbol\pi)\to W(\boldsymbol\pi)$ for every $\boldsymbol\pi\ge0$, $w_{F,n}\to w_F$, and the limit solves the fixed-point equations (18)–(22): for every $\boldsymbol\pi\ge0$,
--   $$W(\boldsymbol\pi)=\min\Big\{\boldsymbol\pi'\mathbf g^P(w_F)+\beta W\big((\mathbf P^P)'\boldsymbol\pi\big),\ (\pi_0+\pi_1)u^R,\ \boldsymbol\pi'\mathbf g^I(w_F)+\beta\big(\pi_0W(\mathbf p_0)+\pi_1W(\mathbf p_1)\big)\Big\},$$
--   with $u^R=c^R+\beta W(\mathbf p_0)$ as in (20) and $w_F=u^R+c^F-c^R$ as in (22) (the third term is absent for $\{P,R\}$, which gives (25)–(28)).
--
--   This is the starting point of the paper's analysis: the optimal solution is characterized as a fixed point, which is then constructed in closed form.
--
--   **Formalization Note** Equations (18)–(21) are stated in the paper for the extreme-point sets $U^*,U^P$; here they are stated for the support function $W(\boldsymbol\pi)=\min_{\mathbf u\in U^*}\boldsymbol\pi'\mathbf u$, which is what $NCoEx$ preserves. The statement does not assert that $W$ is the minimum over a finite set. The added standing ranges $0<\gamma_0,\gamma_1<1$ are part of the hypotheses.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 17, Proposition 2, (18)–(22); p. 19, (25)–(28)

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Proposition 2 (p. 17), value form, with its two-action version (25)–(28) (p. 19): under the
action set {P, R} or {P, I, R}, value iteration from zero converges, for every belief π ≥ 0 and in
the failure coordinate, to a pair (W, w_F) that solves the fixed-point equations (18)–(22) in
support-function form, with u^R = c^R + β W(p0) (20) and w_F = u^R + c^F − c^R (22). -/
theorem proposition_2 (M : Params) (hM : M.Standing) (A : ActSet)
    (hA : A = ActSet.PR ∨ A = ActSet.PIR) :
    ∃ W : Vec → ℝ, ∃ wF : ℝ,
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → Tendsto (fun n => (M.VI A n).1 π) atTop (𝓝 (W π))) ∧
      Tendsto (fun n => (M.VI A n).2) atTop (𝓝 wF) ∧
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → W π = (M.bellman A (W, wF)).1 π) ∧
      wF = (M.cR + M.β * W M.p0) + M.cF - M.cR := by sorry

end MaintPOMDP.Frontier
