-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_pairExpCoordinates_local_inverse
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.pairExpCoordinates_local_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:49:47.862996+00:00
-- url     : https://prove2.me/theorems/8b4efee8-35e5-45bb-8288-1eec60de6d0e
-- title:
--   The map (z, u) ↦ (z, exp_z u) is a local diffeomorphism at every velocity of the injectivity domain (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). `exp x v` is the exponential map at $x$. The **injectivity domain** `injectivityDomain x` is the set of $v \in T_xM$ whose geodesic $t \mapsto \exp_x(tv)$ is still minimizing a little beyond time $1$: some $a > 1$ has $d(x, \exp_x(av)) = a\|v\|$. From the definitions bundles of this split:
--   - `stateChart x` is the preferred chart of the tangent bundle $TM$ at $(x, 0)$, with values in $\mathbb R^n \times \mathbb R^n$ (base point and velocity coordinates);
--   - `geodesicFlow 1` is the time-$1$ geodesic flow on $TM$;
--   - `pairExpCoordinates x y` sends $q = (z, u)$, coordinates of a tangent vector in the chart at $x$, to the pair of the base coordinates $z$ and the coordinates of $\exp_z u$ in the chart at $y$. That is, $(z, u) \mapsto (z, \exp_z u)$ in coordinates;
--   - `pairExpDomain x y` is the set of such $q$ for which this makes sense: $q$ is in the target of `stateChart x`, and the time-$1$ flow lands in the source of `stateChart y`.
--
--   **Statement.** Let $x, y \in M$ and $v$ in the injectivity domain of $x$, with $\exp_x v$ in the source of the chart at $y$. Then there is a partial homeomorphism $e$ of $\mathbb R^n \times \mathbb R^n$ such that
--   - $e$ is `pairExpCoordinates x y` as a function;
--   - the coordinates of $(x, v)$ in `stateChart x` lie in the source of $e$;
--   - the source of $e$ lies in `pairExpDomain x y`;
--   - $e^{-1}$ is $C^\infty$ on the target of $e$.
--
--   So the map $\Psi(z, u) = (z, \exp_z u)$ of the paper's (2.3), from $TM$ to $M \times M$, is a local diffeomorphism near every velocity of the injectivity domain. This is used in the paper's Lemma 2.1 (interior characterization) and for the smooth branch cost of Section 2.1. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.pairExpCoordinates_local_inverse`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Coordinates/PairExpCoordinates.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Coordinates/PairExpCoordinates.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.pairExpCoordinates_local_inverse)

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

 theorem pairExpCoordinates_local_inverse (x y : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) (hy : exp x v ∈ (chartAt (Model n) y).source) :
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y ∧
      stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source ∧
      e.source ⊆ pairExpDomain (n := n) x y ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
