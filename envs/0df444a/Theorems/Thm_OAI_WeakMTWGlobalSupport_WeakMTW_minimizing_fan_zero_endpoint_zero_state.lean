-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_minimizing_fan_zero_endpoint_zero_state
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.minimizing_fan_zero_endpoint_zero_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:49:27.106605+00:00
-- url     : https://prove2.me/theorems/e6f2e1ba-ecc1-4398-b4f2-d147b7b08b80
-- title:
--   Along a geodesic minimizing beyond time 1, a fan with stationary endpoint has stationary endpoint state (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`). From the definitions bundles of this split:
--   - `geodesic p` is the complete geodesic with initial state $p \in TM$, and `geodesicFlow t` is the geodesic flow on $TM$;
--   - `stateChart x` is the preferred chart of $TM$ at $(x, 0)$, with values in $\mathbb R^n \times \mathbb R^n$ (position and velocity coordinates);
--   - for a curve $P : \mathbb R \to TM$ of initial states, the **fan** is $(t, s) \mapsto$ `geodesicFlow t (P s)`;
--   - `fanCoordinates x P (t, s)` is the fan's state in `stateChart x`, and `fanDomain x P` is the set of $(t, s)$ where the state lies in the chart's source.
--
--   **Statement.** Let $x, b \in M$ and let $P : \mathbb R \to TM$ be a $C^\infty$ curve of tangent vectors all based at $b$. Suppose that:
--   - the geodesic of $P(0)$ is minimizing up to some time $L > 1$, that is, $d(b, \gamma_{P(0)}(L)) = L\,\|P(0)\|$;
--   - $(1, 0) \in$ `fanDomain x P`;
--   - the position coordinates $s \mapsto$ (`fanCoordinates x P (1, s)`)$_1$ have derivative $0$ at $s = 0$.
--
--   Then the full state coordinates $s \mapsto$ `fanCoordinates x P (1, s)` have derivative $0$ at $s = 0$.
--
--   So if a variation of a geodesic that still minimizes beyond time $1$ keeps its time-$1$ endpoint fixed to first order, it also keeps the time-$1$ velocity fixed to first order. This is the analytic core of the "no corner" step in the paper's Lemma 2.1 (interior characterization), in the form used to show that interior velocities are nonconjugate. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.minimizing_fan_zero_endpoint_zero_state`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/ExtendedMinimizers.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/ExtendedMinimizers.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.minimizing_fan_zero_endpoint_zero_state)

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
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem minimizing_fan_zero_endpoint_zero_state (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (b : M) (hbase : ∀ s, (P s).1 = b) {L : ℝ} (hL : 1 < L)
    (hmin : dist b (geodesic (P 0) L) = L*‖(P 0).2‖)
    (hx : (1,0) ∈ fanDomain x P)
    (hc : HasDerivAt (fun s => (fanCoordinates x P (1,s)).1) 0 0) :
    HasDerivAt (fun s => fanCoordinates x P (1,s)) 0 0 := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
