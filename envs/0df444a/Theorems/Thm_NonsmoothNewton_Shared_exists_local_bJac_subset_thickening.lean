-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_exists_local_bJac_subset_thickening
-- name    : NonsmoothNewton.Shared.exists_local_bJac_subset_thickening
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:43:59.442986+00:00
-- url     : https://prove2.me/theorems/6a9561ce-0d99-4830-ae08-b95c64404635
-- title:
--   Local upper semicontinuity of the B-Jacobian
-- statement:
--   Let $F : E \to G$ be locally Lipschitz at $x$, with $E$, $G$ finite-dimensional real normed spaces, and let $\partial_B F(y)$ denote the B-limit set `bJac F y`.
--
--   For every $\varepsilon > 0$ there exists $\delta > 0$ such that whenever $y$ satisfies $\mathrm{dist}(y, x) < \delta$, every element of $\partial_B F(y)$ is within $\varepsilon$ of some element of $\partial_B F(x)$. Equivalently, $\partial_B F(y) \subseteq \operatorname{thickening}(\varepsilon, \partial_B F(x))$ for all such $y$.
--
--   This is the qualitative upper semicontinuity of the B-limit set at a point. It is what allows a pointwise assertion about the generalized Jacobian at $x$ to be strengthened to a statement uniform over a neighbourhood, which is exactly what the local convergence theorem for the nonsmooth Newton method requires.
--
--   **Formalization Note** `Metric.thickening ε S` is the open `ε`-neighbourhood of a set, and `Metric.mem_thickening_iff` reads membership as `∃ z ∈ S, dist x z < ε`. The proof is by contradiction: `exists_local_bJac_control` gives a uniform bound on `‖V‖` for `V ∈ bJac F y` over a ball about $x$, so a sequence of counterexample Jacobians approaching $x$ has a convergent subsequence in the finite-dimensional space of continuous linear maps. Its limit lies in `bJac F x` by `bJac_mem_of_tendsto`, so the subsequence eventually falls inside the `ε`-thickening, contradicting the choice of the counterexamples.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Qualitative upper semicontinuity of the B-limit set and, by convex-hull lifting, of Clarke's generalized Jacobian; the step that turns pointwise invertibility at a root into a uniform local inverse bound.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- Local upper semicontinuity of the B-limit set `bJac F`.

For every `ε > 0` there is a radius `δ > 0` about `x` such that every element of
`bJac F y`, for `y` within `δ` of `x`, lies in the `ε`-thickening of `bJac F x`.
This is the qualitative upper semicontinuity needed to turn a pointwise
invertibility statement at `x` into a uniform inverse-norm bound over a whole
neighbourhood, and is the step that `NonsmoothNewton.Local.prop_3_1` requires.

The proof is by contradiction. The local B-Jacobian control
`exists_local_bJac_control` bounds `‖V‖` for `V ∈ bJac F y` uniformly over a
ball about `x`, so any sequence of counterexample Jacobians whose base points
approach `x` has a convergent subsequence by Bolzano–Weierstrass. Its limit `W`
is again in `bJac F x` by the sequential closed graph `bJac_mem_of_tendsto`, so
the subsequence eventually lies in the `ε`-thickening, contradicting how the
counterexamples were chosen. -/
theorem exists_local_bJac_subset_thickening {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, dist y x < δ →
      bJac F y ⊆ Metric.thickening ε (bJac F x) := by sorry

end NonsmoothNewton.Shared
