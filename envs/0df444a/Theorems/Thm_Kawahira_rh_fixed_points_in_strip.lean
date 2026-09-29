-- Prove2me | Theorems.Thm_Kawahira_rh_fixed_points_in_strip
-- name    : Kawahira.rh_fixed_points_in_strip
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:42:10.625361+00:00
-- url     : https://prove2.me/theorems/6208ccda-b221-4c44-84c4-1840a16071bf
-- title:
--   Proposition 8 — under RH, the fixed points of $\nu_\zeta$ in the strip
-- statement:
--   Assume the Riemann hypothesis: every non-trivial zero of $\zeta$ has real part $1/2$. Let $\alpha$ be a fixed point of $\nu_\zeta$ in the open critical strip $S$. Then $\alpha$ is a zero of $\zeta$ lying on the critical line, and moreover:
--
--   1. if $\alpha$ is a simple zero of $\zeta$, then $\alpha$ is an indifferent fixed point of $\nu_\zeta$, i.e. $|\nu_\zeta'(\alpha)| = 1$;
--   2. if $\alpha$ is a multiple zero, then $\alpha$ is an attracting fixed point, i.e. $|\nu_\zeta'(\alpha)| < 1$.
--
--   The mechanism is the index: a zero of order $m$ at $\alpha$ gives index $m\alpha$ with real part $m/2$, which equals $1/2$ exactly when $m = 1$ and is at least $1$ when $m \ge 2$. So under the Riemann hypothesis alone, a hypothetical multiple zero would show up as an attractor of the dynamical system, and the simplicity hypothesis is precisely the statement that no such attractor exists.
--
--   **Formalization Note** $\zeta$ has no pole in the strip, so every fixed point there comes from a zero; simplicity of the zero is expressed as $\zeta'(\alpha) \neq 0$, and the guard $\zeta(\alpha) = 0 \vee \zeta'(\alpha) \neq 0$ excludes the poles of the Lean total function $\nu_\zeta$.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem rh_fixed_points_in_strip
    (hRH : ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2)
    (a : ℂ) (ha0 : 0 < a.re) (ha1 : a.re < 1)
    (hreg : riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) (hfix : nuZeta a = a) :
    riemannZeta a = 0 ∧ a.re = 1 / 2 ∧
      (deriv riemannZeta a ≠ 0 → IsIndifferentFixedPoint nuZeta a) ∧
      (deriv riemannZeta a = 0 → IsAttractingFixedPoint nuZeta a) := by sorry

end Kawahira
