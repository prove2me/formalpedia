-- Prove2me | Theorems.Thm_Kawahira_indifferent_in_strip_implies_rh_and_simplicity
-- name    : Kawahira.indifferent_in_strip_implies_rh_and_simplicity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:42:38.282258+00:00
-- url     : https://prove2.me/theorems/fe07486f-ff38-4ab3-ae9a-04ccf661654b
-- title:
--   Proposition 9 — indifference in the strip implies RH and simplicity
-- statement:
--   Suppose every fixed point of $\nu_\zeta$ in the open critical strip $S$ is indifferent. Then both the Riemann hypothesis and the simplicity hypothesis hold: every non-trivial zero $s$ of $\zeta$ satisfies $\operatorname{Re} s = 1/2$ and $\zeta'(s) \neq 0$.
--
--   This is the converse direction of the paper's Theorem 1 and the place where the functional equation is indispensable. If $\alpha \in S$ is a zero of order $m$, the index of $\nu_\zeta$ at $\alpha$ is $m\alpha$, and indifference forces $m\operatorname{Re}\alpha = 1/2$. By the functional equation $1 - \alpha$ is also a zero of order $m$, lying in $S$, with index $m(1-\alpha)$, and indifference there forces $m(1 - \operatorname{Re}\alpha) = 1/2$ as well. Adding the two gives $m = 1$, and then $\operatorname{Re}\alpha = 1/2$.
--
--   **Formalization Note** The hypothesis is stated for all points of the open strip satisfying the regularity guard $\zeta(\alpha) = 0 \vee \zeta'(\alpha) \neq 0$, which excludes only the poles of the Lean total function $\nu_\zeta$. The conclusion quantifies over all non-trivial zeros; that these lie in the strip is part of the work.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem indifferent_in_strip_implies_rh_and_simplicity
    (h : ∀ a : ℂ, 0 < a.re → a.re < 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
      nuZeta a = a → IsIndifferentFixedPoint nuZeta a) :
    ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0 := by sorry

end Kawahira
