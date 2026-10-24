-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_collision_strict_gap
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.collision_strict_gap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:50:12.844516+00:00
-- url     : https://prove2.me/theorems/e993129c-ba99-481a-979e-8ed04aa0923c
-- title:
--   Strict second-order gap in a collision direction under weak MTW (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the statement `OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits` of this split. $M$ is a compact Riemannian manifold, with finitely many targets $y_i$ and heights $h_i$ (a nonempty finite index type) defining the potential $u = \max_i (h_i - c(\cdot, y_i))$. An active representation $R$ of a tangent vector $p = (p_1, p_2)$ (`ActiveRepresentation y h p`) writes $p_2 = \sum_i \theta_i a_i$ as a convex combination of active velocities. `activeHull y h x` is the convex hull of the active velocities at $x$. Action branches (`ActionBranch`) are smooth local inverses of the pair exponential map, with value the branch cost. From the published goal bundle come the injectivity domain $I(x)$ (`injectivityDomain`) and the weak MTW condition (`HasWeakMTW`). `tangentChartLinear x` identifies $T_xM$ with $\mathbb R^n$ through the chart at $x$.
--
--   **Statement.** Assume weak MTW. Let $p$ be a tangent vector with an active representation $R$ (velocities $a_i$, weights $\theta_i$), let $\xi \in T_{p_1}M$ with $\xi \neq 0$, and let $0 \le s < \ell < 1$. Suppose $r a \in I(p_1)$ for all $0 \le r < s$ and all $a$ in the active hull at $p_1$. Let $B$ be an action branch from $p_1$ to $\exp_{p_1}(s p_2)$ containing the state $(p_1, s p_2)$. For each $i$, let $C_i$ be an action branch from $p_1$ to $\exp_{p_1}(\ell a_i)$ containing the state $(p_1, \ell a_i)$. Write $\partial_\xi$ for the derivative in the first endpoint in the direction of the chart vector of $\xi$, at the chart points of $p_1$ and the respective endpoint. If
--   $$\partial_\xi B - \tfrac{s}{\ell}\,\partial_\xi C_i \le 0 \quad\text{for every } i,$$
--   then
--   $$0 < \sum_i \theta_i\bigl(\partial_\xi^2 B - \tfrac{s}{\ell}\,\partial_\xi^2 C_i\bigr).$$
--
--   This is the strict inequality $\delta_* > 0$ of the paper's equation (4.10) in the proof of Lemma 4.6 ("Local injectivity of the projection"). The first-order hypothesis forces the positive-weight active velocities into a hyperplane perpendicular to $\xi$, and there the transverse gap applies. Together with `OAI.WeakMTWGlobalSupport.WeakMTW.branch_collision_limits` it rules out collisions. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.collision_strict_gap`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Support/CollisionStrictGap.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Support/CollisionStrictGap.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.collision_strict_gap)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem collision_strict_gap (y : ι → M) (h : ι → ℝ)
    (hMTW : HasWeakMTW (n := n) (M := M))
    {p : TangentBundle (model n) M} (R : ActiveRepresentation y h p)
    {ξ : TangentSpace (model n) p.1} (hξ : ξ ≠ 0)
    {s ℓ : ℝ} (hs : 0 ≤ s) (hsℓ : s < ℓ) (hℓ₁ : ℓ < 1)
    (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p.1, r•a ∈ injectivityDomain p.1)
    (B : ActionBranch (n := n) p.1 (exp p.1 (s•p.2)))
    (hB : stateChart p.1 (mulState s p) ∈ B.coord.source)
    (C : ∀ i, ActionBranch (n := n) p.1 (exp p.1 (ℓ•R.a i)))
    (hC : ∀ i, stateChart p.1 (⟨p.1,ℓ•R.a i⟩ : TangentBundle (model n) M) ∈ (C i).coord.source)
    (hfirst : ∀ i, fderiv ℝ B.value (chartAt (Model n) p.1 p.1,
        chartAt (Model n) (exp p.1 (s•p.2)) (exp p.1 (s•p.2))) (tangentChartLinear p.1 ξ,0) -
      (s/ℓ)*fderiv ℝ (C i).value (chartAt (Model n) p.1 p.1,
        chartAt (Model n) (exp p.1 (ℓ•R.a i)) (exp p.1 (ℓ•R.a i))) (tangentChartLinear p.1 ξ,0) ≤ 0) :
    0 < ∑ i, R.θ i*(fderiv ℝ (fderiv ℝ B.value)
      (chartAt (Model n) p.1 p.1,chartAt (Model n) (exp p.1 (s•p.2)) (exp p.1 (s•p.2)))
      (tangentChartLinear p.1 ξ,0) (tangentChartLinear p.1 ξ,0) -
      (s/ℓ)*fderiv ℝ (fderiv ℝ (C i).value)
        (chartAt (Model n) p.1 p.1,chartAt (Model n) (exp p.1 (ℓ•R.a i)) (exp p.1 (ℓ•R.a i)))
        (tangentChartLinear p.1 ξ,0) (tangentChartLinear p.1 ξ,0)) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
