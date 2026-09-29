-- Prove2me | Theorems.Thm_Kawahira_fixed_point_off_strip_repelling
-- name    : Kawahira.fixed_point_off_strip_repelling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:41:41.254302+00:00
-- url     : https://prove2.me/theorems/172d55e2-6434-4dd6-92f9-94c2367e4771
-- title:
--   Proposition 7 — fixed points of $\nu_\zeta$ outside the critical strip are repelling
-- statement:
--   Let $\alpha$ be a fixed point of $\nu_\zeta$ lying outside the open critical strip $S = \{s : 0 < \operatorname{Re} s < 1\}$, with $\alpha \neq 0$ and $\alpha \neq 1$. Then $\alpha$ is repelling:
--   $$|\nu_\zeta'(\alpha)| > 1 .$$
--
--   The reason is that such a fixed point can only be a trivial zero $\alpha = -2k$. These are simple, so the index is $\alpha$ itself, a negative real number, whose real part is certainly less than $1/2$; by the classification of Proposition 4 the fixed point is repelling. Together with the (excluded) pole at $s = 1$, which is also repelling, this confines all the interesting dynamics of $\nu_\zeta$ to the critical strip.
--
--   **Formalization Note** The hypotheses $\alpha \neq 0$, $\alpha \neq 1$ and $\zeta(\alpha) = 0 \vee \zeta'(\alpha) \neq 0$ exclude the points at which the total function $\nu_\zeta$ of Lean does not model the meromorphic map: the origin, the pole of $\zeta$, and the poles of $\nu_\zeta$. The paper's statement also covers the pole $s=1$, where the fixed point is likewise repelling.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem fixed_point_off_strip_repelling (a : ℂ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hreg : riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0)
    (hout : ¬ (0 < a.re ∧ a.re < 1)) (hfix : nuZeta a = a) :
    IsRepellingFixedPoint nuZeta a := by sorry

end Kawahira
