-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_initialCost_geometry
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.initialCost_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:44:54.321024+00:00
-- url     : https://prove2.me/theorems/e24e9421-87b9-44f5-a429-988b62182bb6
-- title:
--   Smoothness, gradient and radial Hessian identity of the cost at an injectivity velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`:
--   - $M$ is a compact smooth Riemannian manifold modelled on $\mathbb R^n$, whose distance is the Riemannian distance.
--   - $c = d^2/2$ is the cost.
--   - `injectivityDomain x` is $I(x)$, the velocities $v \in T_xM$ with $d(x, \exp_x(av)) = a\|v\|$ for some $a > 1$.
--
--   In the chart at $x$:
--   - `initialCost x y` is $a \mapsto c(\text{chart}_x^{-1}(a), y)$.
--   - `metric x a` is the metric at the coordinate point $a$.
--   - `tangentChartLinear x` identifies $T_xM$ with $\mathbb R^n$. Write $\hat v$ for the image of $v$, and $\bar x$ for the coordinate of $x$.
--   - For a metric field $G$, a function $f$, a point $a$ and a vector $\nu$, `actionForm G f a ν` is the bilinear form $(u, w) \mapsto D^2 f(a)(u, w) + \Gamma^\flat_a(u, w)(\nu)$. Here $\Gamma^\flat_a(u, w)(z) = \tfrac12\bigl(DG_a(u)(w, z) + DG_a(w)(u, z) - DG_a(z)(u, w)\bigr)$ (`lowerChristoffel`).
--
--   **Statement.** Let $v \in I(x)$ and $f = $ `initialCost x (exp x v)`. Then:
--   1. $f$ is $C^\infty$ at $\bar x$;
--   2. $Df(\bar x)\,w = -\,\mathrm{metric}_x(\bar x)(\hat v, w)$ for every $w$;
--   3. $\mathrm{actionForm}(\mathrm{metric}_x, f, \bar x, \hat v)(w, \hat v) = \mathrm{metric}_x(\bar x)(w, \hat v)$ for every $w$.
--
--   Item 1 is the smoothness of the cost near $(x, \exp_x v)$ from Lemma 2.1 of the paper, item 2 is the first-variation formula $\nabla_x \hat c(x, \exp_x w) = -w$ of its Section 2.1, and item 3 is the identity $A_x(w)(w, \cdot) = \langle w, \cdot\rangle_x$ (2.5), with the arguments of the symmetric form $A_x(w)$ written in the other order. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.initialCost_geometry`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Variations/ActionHessian.lean`). The definitions come from the published goal bundle `Def_WeakMTWGlobalSupport` and from the definitions bundles `OAIQWMTW001` and `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Variations/ActionHessian.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.initialCost_geometry)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW001
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
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem initialCost_geometry (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (initialCost x (exp x v)) (chartAt (Model n) x x) ∧
    (∀ w, fderiv ℝ (initialCost x (exp x v)) (chartAt (Model n) x x) w =
      -metric x (chartAt (Model n) x x) (tangentChartLinear x v) w) ∧
    (∀ w, actionForm (metric x) (initialCost x (exp x v)) (chartAt (Model n) x x)
      (tangentChartLinear x v) w (tangentChartLinear x v) =
        metric x (chartAt (Model n) x x) w (tangentChartLinear x v)) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
