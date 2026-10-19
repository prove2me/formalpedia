-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_exists_minimizing_vector
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.exists_minimizing_vector
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:53.360684+00:00
-- url     : https://prove2.me/theorems/a7f2aa7c-bb0f-4b1f-8059-9ec07c3eb17a
-- title:
--   Hopf–Rinow on a compact Riemannian manifold: every two points are joined by a minimizing geodesic
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). A **complete geodesic** with initial data $(x, v)$ is a smooth curve $\gamma : \mathbb R \to M$ with $\gamma(0) = x$ and $\gamma'(0) = v$ that near every time realizes distance at constant speed: $d(\gamma(s), \gamma(r)) = \|v\|\,|s - r|$ for $s, r$ close to $t$ (`CompleteGeodesicWithInitialData`). The exponential map `exp x v` is $\gamma(1)$ for such a geodesic, when one exists.
--
--   **Statement.** For all $x, y \in M$ there is a tangent vector $v \in T_xM$ with
--   $$\exp_x v = y \quad\text{and}\quad \|v\| = d(x, y).$$
--
--   So every two points of a compact Riemannian manifold are joined by a minimizing geodesic, of length their distance. This is the existence part of the Hopf–Rinow theorem (Hopf and Rinow 1931) for compact manifolds, in the form OpenAI's paper uses. The statement imports only the published goal bundle `Def_WeakMTWGlobalSupport`. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.exists_minimizing_vector`, OpenAI's theorem of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/HopfRinow.lean`).
-- source:
--   Hopf and Rinow, Über den Begriff der vollständigen differentialgeometrischen Fläche, Comment. Math. Helv. 3 (1931); Lean: OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/HopfRinow.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.exists_minimizing_vector)

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

theorem OAI.WeakMTWGlobalSupport.WeakMTW.exists_minimizing_vector
    {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
    [IsManifold (model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
    [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
    [IsRiemannianManifold (model n) M] [CompactSpace M] (x y : M) :
    ∃ v : TangentSpace (model n) x, exp x v = y ∧ ‖v‖ = dist x y := by
  sorry
