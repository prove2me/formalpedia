-- Prove2me | Theorems.Thm_Kawahira_newton_at_zero_of_order
-- name    : Kawahira.newton_at_zero_of_order
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:38:15.068218+00:00
-- url     : https://prove2.me/theorems/ecd93de6-dc90-4427-9970-589ff5973d17
-- title:
--   Proposition 13 — the Newton map at a zero of order $m$: $N_g'(\alpha) = 1 - \frac{1}{m}$
-- statement:
--   Let $g$ be analytic at $\alpha$ with a zero of order $m \ge 1$ there. Then $\alpha$ is a fixed point of the Newton map
--   $$N_g(z) = z - \frac{g(z)}{g'(z)},$$
--   with multiplier
--   $$N_g'(\alpha) = 1 - \frac{1}{m},$$
--   so that the index is $\iota(N_g,\alpha) = m$ and the fixed point is attracting for every $m \ge 1$ (superattracting when $m = 1$).
--
--   This is the contrast that explains the design of the nu function. Newton's method converts *every* zero of $g$ into an attracting fixed point, irrespective of its position, which is exactly what makes it a root-finding algorithm and exactly what makes it blind to the Riemann hypothesis; the index is the order $m$, a positive integer, and carries no information about the location of the zero. The nu function multiplies the index by $\alpha$, and that is where the critical line enters.
--
--   **Formalization Note** As with the nu function, for $m \ge 2$ the quotient $g/g'$ has a removable singularity at $\alpha$ and the Lean total function takes the correct value there.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem newton_at_zero_of_order (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    newton g a = a ∧ deriv (newton g) a = 1 - 1 / (m : ℂ) := by sorry

end Kawahira
