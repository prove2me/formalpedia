-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_WeakMTW_short_fan_bridge
-- name    : OAI.WeakMTWGlobalSupport.WeakMTW.short_fan_bridge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T12:50:18.397156+00:00
-- url     : https://prove2.me/theorems/634975ae-1f2c-4b24-a889-13fb550ccb77
-- title:
--   Short final segments of a geodesic fan have smooth chart cost with first-variation derivative (OpenAI weak MTW)
-- statement:
--   **Setting.** As in the published goal bundle `Def_WeakMTWGlobalSupport`: $M$ is a compact smooth manifold modelled on $\mathbb R^n$ (`Model n`) with a smooth Riemannian metric, whose metric-space distance is the Riemannian distance (Mathlib's `IsRiemannianManifold`), and `cost` $= d^2/2$. From the definitions bundles of this split, for a point $x$:
--   - `stateChart x` is the preferred chart of $TM$ at $(x, 0)$, with values in $\mathbb R^n \times \mathbb R^n$;
--   - `chartCost x` is the cost read in the chart at $x$, $(a, b) \mapsto \mathrm{cost}(\varphi_x^{-1}a, \varphi_x^{-1}b)$, and `metric x` is the coordinate metric;
--   - `flowCoordinates x t q` is the time-$t$ geodesic flow of the state with coordinates $q$, read in `stateChart x`;
--   - for a curve $P : \mathbb R \to TM$ of initial states, `fanCoordinates x P (t, s)` is the state of the fan `geodesicFlow t (P s)` in `stateChart x`, and `fanDomain x P` is the set of $(t, s)$ where that state lies in the chart's source.
--
--   `ShortChartAction x t q` says that the time-$t$ segment starting at the state $q = (q_1, q_2)$ behaves like a minimizing segment in the chart. That is: $q$ is in the chart's target; the time-$t$ flow stays in the chart, ending at position $p_1$ with velocity $p_2$; `chartCost x` is $C^\infty$ near $(q_1, p_1)$; and its derivative there is the first-variation formula
--   $$D(\mathrm{chartCost}_x)(q_1, p_1)(w_1, w_2) = t\,\bigl(g_{p_1}(p_2, w_2) - g_{q_1}(q_2, w_1)\bigr).$$
--
--   **Statement.** Let $x \in M$, let $P : \mathbb R \to TM$ be $C^\infty$ with $(1, 0) \in$ `fanDomain x P`, and let $k > 0$. Then there is $\varepsilon$ with $0 < \varepsilon < k$ such that:
--   - for all $s$ near $0$, both $(1 - \varepsilon, s)$ and $(1, s)$ lie in `fanDomain x P`, and `ShortChartAction x ε` holds at the fan's state at time $1 - \varepsilon$;
--   - `ShortChartAction x ε` also holds at the fan's state at time $1$ for $s = 0$.
--
--   So short final pieces of a geodesic fan have a smooth chart cost with the first-variation derivative. This is the local input to the "no corner" argument of the paper's Lemma 2.1. Lean: `OAI.WeakMTWGlobalSupport.WeakMTW.short_fan_bridge`, OpenAI's lemma of that name (in `lean/OAI/Geometry/WeakMTW/Geodesics/ShortFan.lean`). The definitions come from the published bundle `Def_WeakMTWGlobalSupport` and the definitions bundle `OAIQWMTW003` of this split.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/ShortFan.lean (declaration OAI.WeakMTWGlobalSupport.WeakMTW.short_fan_bridge)

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

 theorem short_fan_bridge (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (h₀ : (1,0) ∈ fanDomain x P) {k : ℝ} (hk : 0 < k) :
    ∃ ε : ℝ, 0 < ε ∧ ε < k ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), (1-ε,s) ∈ fanDomain x P ∧ (1,s) ∈ fanDomain x P ∧
        ShortChartAction x ε (fanCoordinates x P (1-ε,s))) ∧
      ShortChartAction x ε (fanCoordinates x P (1,0)) := by
  sorry

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end
