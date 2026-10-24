-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_cost_first_limit
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T03:00:02.942876+00:00
-- url     : https://prove2.me/theorems/6b8808b3-62f5-47b9-829b-8a7450b6ffb7
-- title:
--   First variation of the squared-distance cost in the first point, uniformly near an interior endpoint (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). The other objects:
--   - `cost x y` $= d(x, y)^2/2$, and `exp x v` is the exponential map;
--   - the **injectivity domain** `injectivityDomain x` is the set of $v \in T_xM$ whose geodesic $t \mapsto \exp_x(tv)$ is still minimizing a little beyond time $1$: some $a > 1$ has $d(x, \exp_x(av)) = a\|v\|$;
--   - $\varphi_x$ is the preferred chart at $x$ (`chartAt (Model n) x`);
--   - `tangentChartLinear x` is its differential at $x$, from the definitions bundle `OAIQWMTW002`; it identifies $T_xM$ with $\mathbb R^n$.
--
--   **Statement.** Let $v$ be in the injectivity domain of $x$ and $\xi \in T_xM$. Let $z_j \to \exp_x v$ in $M$, and let $l_j \to 0$ be real numbers that are eventually nonzero. Put $x_j = \varphi_x^{-1}\bigl(\varphi_x(x) + l_j\, d\varphi_x(\xi)\bigr)$, the point reached from $x$ by moving $l_j\xi$ in the chart. Then
--   $$\frac{\mathrm{cost}(x_j, z_j) - \mathrm{cost}(x, z_j)}{l_j} \;\longrightarrow\; -\langle v, \xi\rangle .$$
--
--   So the cost is differentiable in its first point near $(x, \exp_x v)$, with gradient $-v$, uniformly as the second point moves. This is the first-variation formula $\nabla_x c(x, \exp_x w) = -w$ of the paper's Section 2.1, at interior velocities, where the cost is smooth near the pair by the paper's Lemma 2.1. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Coordinates/CostFirstTaylor.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW002` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Coordinates/CostFirstTaylor.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.cost_first_limit)

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

 theorem cost_first_limit (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (ξ : TangentSpace (model n) x)
    {z : ℕ → M} (hz : Tendsto z atTop (𝓝 (exp x v)))
    {l : ℕ → ℝ} (hl : Tendsto l atTop (𝓝 0)) (hne : ∀ᶠ j in atTop, l j ≠ 0) :
    Tendsto (fun j => (cost ((chartAt (Model n) x).symm
      (chartAt (Model n) x x + l j • tangentChartLinear x ξ)) (z j) - cost x (z j)) / l j)
      atTop (𝓝 (-inner ℝ v ξ)) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
