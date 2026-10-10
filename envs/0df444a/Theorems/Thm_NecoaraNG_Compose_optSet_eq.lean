-- Prove2me | Theorems.Thm_NecoaraNG_Compose_optSet_eq
-- name    : NecoaraNG.Compose.optSet_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:32.953254+00:00
-- url     : https://prove2.me/theorems/03d9088b-15ce-4a70-85e3-0741c57c001c
-- title:
--   Proof of Theorem 8, p. 15 — the optimal set of (38) is the polyhedron {x : Ax = t*, Cx ≤ d}
-- statement:
--   Under the assumptions of Theorem 8 (problem (38) with $g$ differentiable, $\sigma_g$-strongly convex, with $L_g$-Lipschitz gradient, $A\ne0$), let $x^*$ be an optimal point and $t^*=Ax^*$. Then the optimal set is the polyhedron
--   $$X^*=\{x: Ax=t^*,\ Cx\le d\}.$$
--
--   The description of $X^*$ by linear equalities and inequalities is what allows the Hoffman inequality to bound the distance to $X^*$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 15, proof of Theorem 8, display X* = {x* : Ax* = t*, Cx* ≤ d}

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace NecoaraNG.Compose

theorem optSet_eq {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (hA : A ≠ 0) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (d : NecoaraNG.Chain.E p)
    (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (σg Lg : ℝ) (hσg : 0 < σg)
    (hg : StrongConvexOn Set.univ σg g)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x))) :
    NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)) =
      {x | A x = A xstar ∧ ∀ i, C x i ≤ d i} := by sorry

end NecoaraNG.Compose
