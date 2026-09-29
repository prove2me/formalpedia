-- Prove2me | Theorems.Thm_Kawahira_riemann_hypothesis_iff_nu_zeta
-- name    : Kawahira.riemann_hypothesis_iff_nu_zeta
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:49:17.108588+00:00
-- url     : https://prove2.me/theorems/936a807b-ea69-4f0b-a7e1-3ba3525f2908
-- title:
--   Theorem 1 — RH and simplicity $\iff$ $\nu_\zeta$ has no attracting fixed point
-- statement:
--   This is Theorem 1 of Kawahira (2016), in its analytic part. Write
--   $$\nu_\zeta(z) \;=\; z - \frac{\zeta(z)}{z\,\zeta'(z)},$$
--   a meromorphic function on $\mathbb{C}$. The following three conditions are equivalent.
--
--   **(a)** The Riemann hypothesis is true and every non-trivial zero of $\zeta$ is simple: every non-trivial zero $s$ satisfies $\operatorname{Re} s = 1/2$ and $\zeta'(s) \neq 0$.
--
--   **(b)** Every non-trivial zero of $\zeta$ is an indifferent fixed point of $\nu_\zeta$: $\nu_\zeta(s) = s$ and $|\nu_\zeta'(s)| = 1$.
--
--   **(c)** $\nu_\zeta$ has no attracting fixed point: there is no $\alpha$ with $\nu_\zeta(\alpha) = \alpha$ and $|\nu_\zeta'(\alpha)| < 1$.
--
--   The equivalence rests on the holomorphic index. A zero of $\zeta$ of order $m$ at $\alpha$ is a fixed point of $\nu_\zeta$ of index $m\alpha$, and a fixed point is attracting, indifferent or repelling according to whether the real part of its index exceeds, equals or falls below $1/2$. So indifference at $\alpha$ says $m\operatorname{Re}\alpha = 1/2$, and the symmetry $\alpha \mapsto 1-\alpha$ of the non-trivial zeros — a consequence of the functional equation — upgrades this to $m = 1$ and $\operatorname{Re}\alpha = 1/2$. The trivial zeros and the pole of $\zeta$ contribute repelling fixed points only, so they cannot interfere with (c).
--
--   **Formalization Note** In (c) the quantifier carries the guards $\alpha \neq 0$, $\alpha \neq 1$ and $\zeta(\alpha) = 0 \vee \zeta'(\alpha) \neq 0$: these exclude the origin, the pole of $\zeta$ — a repelling fixed point in the paper's account — and the poles of $\nu_\zeta$, which are exactly the points where the Lean total function does not model the meromorphic map. Conditions (d) and (e) of the paper (topological disks and their homeomorphic deformations) are not part of this statement; see the mission's formalization scope.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem riemann_hypothesis_iff_nu_zeta :
    ((∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0) ↔
        (∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s)) ∧
      ((∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s) ↔
        (∀ a : ℂ, a ≠ 0 → a ≠ 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
          ¬ IsAttractingFixedPoint nuZeta a)) := by sorry

end Kawahira
