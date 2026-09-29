-- Prove2me | Theorems.Thm_Kawahira_xi_variant
-- name    : Kawahira.xi_variant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:43:07.486594+00:00
-- url     : https://prove2.me/theorems/848e4a93-e98d-4c7d-be59-71eb90b47f56
-- title:
--   Theorem 11 — the variant for the Riemann xi function: all fixed points of $\nu_\xi$ indifferent
-- statement:
--   Let $\xi$ be the Riemann xi function, the entire function whose zeros are exactly the non-trivial zeros of $\zeta$, with the same orders, and let
--   $$\nu_\xi(z) = z - \frac{\xi(z)}{z\,\xi'(z)} .$$
--   Then the Riemann hypothesis together with the simplicity hypothesis holds if and only if every fixed point of $\nu_\xi$ is indifferent.
--
--   This is condition (b') of the paper's Theorem 11. Because $\xi$ is entire and has neither trivial zeros nor poles, the statement needs no restriction to the critical strip and no separate treatment of exceptional fixed points: the dictionary between the zeros of $\zeta$ and the dynamics of $\nu_\xi$ is exact, which makes this the cleanest of the paper's reformulations.
--
--   **Formalization Note** The guards $\alpha \neq 0$ and $\xi(\alpha) = 0 \vee \xi'(\alpha) \neq 0$ exclude the origin and the poles of $\nu_\xi$, the two places where the Lean total function does not model the meromorphic map. The xi function is taken in Kawahira's normalization $\xi(z) = \frac12 z(1-z)\pi^{-z/2}\Gamma(z/2)\zeta(z)$.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_zeta

open Complex Topology

namespace Kawahira

theorem xi_variant :
    (∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0) ↔
      (∀ a : ℂ, a ≠ 0 → (xi a = 0 ∨ deriv xi a ≠ 0) → nuXi a = a →
        IsIndifferentFixedPoint nuXi a) := by sorry

end Kawahira
