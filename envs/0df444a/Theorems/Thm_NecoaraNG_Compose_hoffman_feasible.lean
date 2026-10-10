-- Prove2me | Theorems.Thm_NecoaraNG_Compose_hoffman_feasible
-- name    : NecoaraNG.Compose.hoffman_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:21.394295+00:00
-- url     : https://prove2.me/theorems/bfe0c400-aec1-4821-b550-f9535185e666
-- title:
--   Proof of Theorem 8, p. 15 — ‖x − x̄‖ ≤ θ(A, C)‖Ax − Ax̄‖ for every feasible x
-- statement:
--   Under the assumptions of Theorem 8, let $x^*$ be optimal and let $\theta>0$ be a Hoffman constant for the polyhedron $\{z: Az=Ax^*,\ Cz\le d\}$ (Euclidean norms). Then for every feasible $x$ (that is, $Cx\le d$) and $\bar x=[x]_{X^*}$,
--   $$\|x-\bar x\|\le\theta\,\|Ax-A\bar x\|.$$
--
--   For feasible points the inequality part of the Hoffman residual vanishes, so the distance to the optimal set is controlled by $A$ alone.
--
--   **Formalization Note** The Hoffman constant is a hypothesis: its existence is Hoffman's 1952 theorem, which the page cites without proof. The hypothesis is the Hoffman inequality for the polyhedron written with $Ax^*$, not for every right-hand side.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 15, proof of Theorem 8, display ‖x − x̄‖ ≤ θ(A, C)‖Ax − Ax̄‖ ∀x ∈ X

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

open scoped InnerProductSpace

namespace NecoaraNG.Compose

theorem hoffman_feasible {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (hA : A ≠ 0) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p)
    (d : NecoaraNG.Chain.E p) (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (σg Lg : ℝ) (hσg : 0 < σg)
    (hg : StrongConvexOn Set.univ σg g)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖)
    (xstar : NecoaraNG.Chain.E n) (hxstar : xstar ∈ NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x)))
    (θ : ℝ) (hθ : 0 < θ) (hHoff : IsHoffmanConst A C (A xstar) d θ) :
    ∀ x ∈ polyhedron C d, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet (polyhedron C d) (fun x => g (A x))) x xbar →
      ‖x - xbar‖ ≤ θ * ‖A x - A xbar‖ := by sorry

end NecoaraNG.Compose
