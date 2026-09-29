-- Prove2me | Theorems.Thm_Kawahira_index_eq_one_div_one_sub_multiplier
-- name    : Kawahira.index_eq_one_div_one_sub_multiplier
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:28:01.132633+00:00
-- url     : https://prove2.me/theorems/9701c7ec-c351-43ac-9ed2-a748391d2e32
-- title:
--   Proposition 3 — holomorphic index in terms of the multiplier: $\iota = \frac{1}{1-\lambda}$
-- statement:
--   Let $g$ be analytic at a point $\alpha$ with $g(\alpha) = \alpha$, and suppose the multiplier $\lambda = g'(\alpha)$ is not equal to $1$. Then for all sufficiently small radii $r > 0$ the holomorphic index of $g$ at $\alpha$, computed on the circle of radius $r$,
--   $$\iota_r(g,\alpha) \;=\; \frac{1}{2\pi i}\oint_{|z-\alpha| = r} \frac{dz}{z - g(z)},$$
--   is independent of $r$ and equals
--   $$\frac{1}{1-\lambda}.$$
--
--   This is the computation that makes the holomorphic index usable: away from the exceptional multiplier $\lambda = 1$, the index carries exactly the information of the multiplier, and the Möbius map $\lambda \mapsto (1-\lambda)^{-1}$ transports the unit disk of attracting multipliers onto the half-plane $\operatorname{Re}\iota > 1/2$. It is the first of the two facts from complex dynamics that the mission's main equivalence rests on.
--
--   **Formalization Note** "For all sufficiently small $r > 0$" is expressed as an eventual statement along the filter of right-neighbourhoods of $0$ in $\mathbb{R}$; no single radius is privileged, and no claim is made for large $r$, where the circle may enclose further fixed points.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem index_eq_one_div_one_sub_multiplier (g : ℂ → ℂ) (a : ℂ)
    (hg : AnalyticAt ℂ g a) (hfix : g a = a) (hlam : deriv g a ≠ 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), holomorphicIndex g a r = 1 / (1 - deriv g a) := by sorry

end Kawahira
