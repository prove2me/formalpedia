-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_radialSplitAction_smooth
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.radialSplitAction_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T03:00:40.105101+00:00
-- url     : https://prove2.me/theorems/4d3c321d-e71d-430e-abd0-ef6421395b60
-- title:
--   Smoothness of the radial split action (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, whose distance is the Riemannian distance, and $c = d^2/2$ is the cost. In addition:
--   - `minimizingDomain x` is $G_x = \{a \in T_xM : d(x, \exp_x a) = \|a\|\}$.
--   - For $a \in T_xM$ and times $s, t$, the **radial split action** `radialSplitAction x a s t` is the function of a chart coordinate $z \in \mathbb R^n$ (a base point near $x$, via the chart at $x$) and a tangent vector $u \in T_xM$ given by
--   $$\frac{c\bigl(\text{chart}_x^{-1}(z),\ \exp_x(sa + u)\bigr)}{s} + \frac{c\bigl(\exp_x(sa + u),\ \exp_x(ta)\bigr)}{t - s} - \frac{c\bigl(\text{chart}_x^{-1}(z),\ \exp_x(ta)\bigr)}{t}.$$
--
--   It compares the action of a two-step path through an intermediate point near $\exp_x(sa)$ with the action of the direct path, each step priced by the cost divided by its time.
--
--   **Statement.** Let $a \in G_x$ and $0 < s < t < 1$. Then the radial split action is $C^\infty$ at $(\bar x, 0)$, where $\bar x$ is the chart coordinate of $x$.
--
--   OpenAI's Lean proof of the strict radial comparison $A_x(sa) > \tfrac{s}{t} A_x(ta)$ (Lemma 2.3 of the paper) uses the Hessian of this function at $(\bar x, 0)$, and this statement supplies its smoothness. Each of the three costs is smooth because both endpoints are joined by a velocity in the injectivity domain, as in Lemma 2.1 of the paper. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.radialSplitAction_smooth`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/RadialSplitAction.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/RadialSplitAction.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.radialSplitAction_smooth)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW002

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
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem radialSplitAction_smooth (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ContDiffAt ℝ ∞ (radialSplitAction x a s t) (chartAt (Model n) x x,0) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
