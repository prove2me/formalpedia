-- Prove2me | Theorems.Thm_MinEarnings_Static_theorem_3
-- name    : MinEarnings.Static.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:46.181881+00:00
-- url     : https://prove2.me/theorems/fd551f6d-eb99-410c-a256-03179945d3a7
-- title:
--   Theorem 3, p. 15 — an M-minimum-earnings marketplace is stable if and only if it is statically stable
-- statement:
--   Let the demand $D$ and supply $S$ satisfy the regularity assumptions of the model (on $[0,\infty)$: $D$ positive, strictly decreasing and continuous; $S$ strictly increasing and continuous, positive and differentiable on $(0,\infty)$), and let $M>0$ be a minimum hourly earnings target. Then
--
--   $$\text{the } M\text{-minimum-earnings marketplace is stable}\iff\text{it is statically stable}.$$
--
--   Here *stable* (Definitions 1–2) means that some feasible policy $(p_t,w_t)$ with equilibrium earnings $z_t=w_t\,u(p_t,z_t)>0$, where $u(p,z)=\min\{D(p),S(z)\}/S(z)$, obeys the rule $w_{t+1}\ge M/u(p_t,z_t)$ in every period, has bounded wages, and has non-negative profit $(p_t-w_t)\min\{D(p_t),S(z_t)\}$ in all but finitely many periods. *Statically stable* (Definition 4) means that the static system
--   $$u=\frac{\min\{D(p),S(z)\}}{S(z)},\qquad z=w\,u,\qquad w\ge \frac{M}{u},\qquad p\ge w$$
--   has a solution with $p,w,z\ge 0$ and $u\in(0,1]$.
--
--   The theorem says that the one-period lag in the utilization used by the regulation does not affect which earnings targets can be sustained: stability can be decided from a single static system.
--
--   **Formalization Note** The standing assumptions that the revenue $R(p)=pD(p)$ is unimodal and that $D$ and $S$ cross (p. 8) are not assumed, since neither the statement nor its proof uses them; the theorem is therefore stated in that generality. The equilibrium condition carries $z_t>0$ to exclude Lean's junk value $0/0=0$ of the utilization at $S(0)=0$. Time is 0-based.
-- source:
--   Asadpour, Lobel & van Ryzin, Minimum Earnings Regulation and the Stability of Marketplaces, SSRN 3502607 (version of August 24, 2022), p. 15, Theorem 3, Definition 4 (8); proof Online Appendix pp. 5–6 (PDF 33–34)

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

namespace MinEarnings.Static

theorem theorem_3 (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M) :
    MinEarnings.Threshold.IsStable D S M ↔ IsStaticallyStable D S M := by sorry

end MinEarnings.Static
