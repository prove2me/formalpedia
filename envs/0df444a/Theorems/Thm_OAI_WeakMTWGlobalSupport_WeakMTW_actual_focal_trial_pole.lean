-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_actual_focal_trial_pole
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:47:21.888985+00:00
-- url     : https://prove2.me/theorems/d68a7613-7208-4ab4-8bce-f3ae011fa1d8
-- title:
--   A conjugate velocity inside a minimizing segment forces a pole of the action Hessian (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, with the Riemannian distance $d$ and the exponential map $\exp$. The minimizing domain of $x$ is $G_x = \{w : d(x, \exp_x w) = \|w\|\}$ (`minimizingDomain`). For $v \in T_xM$, `actionHessian x v` is the bilinear form $A_x(v)$ on $T_xM$: the Hessian at $x$, with the second endpoint $\exp_x v$ held fixed, of the half squared length of the geodesic branch through velocity $v$. In Lean it is written in a chart at $x$ as the covariant Hessian (`actionForm`) of the cost along the branch. A two-parameter family of bilinear forms $A(h, s)$ has a **trial pole** in the direction $\xi$ (`FirstCut.HasTrialPole`) if there are $C$, $c > 0$ and $\delta > 0$ with
--   $$A(h, s)(\xi, \xi) \le C - \frac{c}{s^2 + h} \qquad \text{for all } 0 < h < \delta,\ |s| < \delta .$$
--
--   **Statement.** Let $x \in M$, let $p, e \in T_xM$ and $a, b > 0$, and suppose the whole segment $p + s e$, $s \in [-a, b]$, lies in $G_x$. Let $k \in T_xM$ be a kernel vector of the differential of $\exp_x$ at $p$, read in a chart at $\exp_x p$. Let $\xi \in T_xM$ with $\langle \xi, k\rangle \ne 0$. Then the family
--   $$(h, s) \longmapsto A_x\bigl((1 - h)(p + s e)\bigr)$$
--   has a trial pole in the direction $\xi$.
--
--   This is the trial-field estimate in the proof of the paper's Proposition 3.1, the joint tangential and radial bound (3.3). Testing the index-form representation of $A_x$ on a Jacobi-field trial makes the Hessian blow down like $-c/(t^2 + 1 - r)$ near a conjugate velocity in the interior of a minimizing segment. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/FocalPole.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/FocalPole.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.actual_focal_trial_pole)

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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem actual_focal_trial_pole (x : M) {p e k : TangentSpace (model n) x} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hseg : ∀ s ∈ Icc (-a) b, p+s•e ∈ minimizingDomain x)
    (hk : fderiv ℝ (fun w => chartAt (Model n) (exp x p) (exp x w)) p k = 0)
    (ξ : TangentSpace (model n) x) (hξ : inner ℝ ξ k ≠ 0) :
    FirstCut.HasTrialPole (fun h s => actionHessian x ((1-h)•(p+s•e))) ξ := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
