-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_fibre_kernel_perp_radial
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.fibre_kernel_perp_radial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:57:33.151115+00:00
-- url     : https://prove2.me/theorems/b36eca8b-3565-493a-95d5-1ba6834e769f
-- title:
--   A kernel vector of the differential of the exponential map is orthogonal to the velocity (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). `exp x w` is the exponential map at $x$, and $\langle\cdot,\cdot\rangle$ is the Riemannian inner product on $T_xM$. For a point $y$, $\varphi_y$ is the preferred chart of $M$ at $y$ (`chartAt (Model n) y`).
--
--   **Statement.** Let $x, y \in M$ and $v, k \in T_xM$, with $\exp_x v$ in the source of $\varphi_y$. If the derivative at $v$ of $w \mapsto \varphi_y(\exp_x w)$ vanishes on $k$, then
--   $$\langle k, v\rangle = 0 .$$
--
--   So every vector in the kernel of $d_v \exp_x$ is orthogonal to $v$. This is the step "so $k \perp z$" in the proof of the paper's Proposition 3.1: the Jacobi field $J$ of the variation in the direction $k$ vanishes at both ends, and $\langle J, \dot\gamma\rangle$ is affine with initial slope $\langle k, v\rangle$. No minimality is assumed. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.fibre_kernel_perp_radial`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Coordinates/FocalCoordinates.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport`.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Coordinates/FocalCoordinates.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.fibre_kernel_perp_radial)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport

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
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]

variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem fibre_kernel_perp_radial (x y : M) {v k : TangentSpace (model n) x}
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hk : fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v k = 0) :
    inner ℝ k v = 0 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
