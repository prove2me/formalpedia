-- Prove2me | Theorems.Thm_OAI_QuinticLienard_AxisFlow_axisLambda_gt
-- name    : OAI.QuinticLienard.AxisFlow.axisLambda_gt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:12:05.324035+00:00
-- url     : https://prove2.me/theorems/12dc6ccc-fe43-4c4f-9515-01e507ebf614
-- title:
--   A slope-intercept condition on the quintic profile forces the height-zero fitted slope above d (OpenAI quintic Liénard, cf. Proposition 5.3)
-- statement:
--   **Notation** (definitions bundle `OAIQWQL000` of this split; the paper's Sections 2–3). For $a \in \mathbb R^6$ let $P_a(x) = \sum_{i=0}^{5} a_i x^i$ (`ScaledProfile.poly a`) and, on the right half-plane in the coordinate $u = x^2/2$, let $\varphi_a(u) = P_a(\sqrt{2u})$ be the profile (`QuinticProfile.profile a`). The bundle's formulas give $\varphi_a'(u)$ = `ScaledProfile.slope a u`, $\varphi_a''(u)$ = `ScaledProfile.curvature a u` and $\varphi_a'''(u)$ = `ScaledProfile.third a u` for $u > 0$. An arch of a profile $\varphi$ with base height $h$ and peak height $t > h$ is a solution of $du/dy = \varphi(u) - y$ that rises from $u = h$ to the peak $u(\varphi(t)) = t$ and returns to $h$ (`ScalarArcs.IsArch`); its half-width $r$ is half the distance between its two endpoints $y_<, y_>$, and its midpoint is $M = (y_< + y_>)/2 - \varphi(h)$.
--
--   **The quadratic fit** (the paper's Theorem 3.6). For a profile and a base height $h > 0$, let $M(h, r)$ be the midpoint of the arch with base $h$ and half-width $r$ (`PositiveWidth.midpointAtWidth`, the peak chosen with that width) and $M_r$ its derivative in $r$. The fitted slope $\lambda(h, r)$ and curvature $\kappa(h, r)$ (`QuinticFit.lambda a (h, r)`, `QuinticFit.kappa a (h, r)` for the profile $\varphi_a$) are the parameters $(d, k)$ of the quadratic profile $du + ku^2/2$ whose arch of half-width $r$ has the same midpoint $M$ and the same $r$-derivative $M_r$ (`QuadraticFit.fitD`, `QuadraticFit.fitK`; they are set to $0$ where no such parameters exist).
--
--   **Height zero.** For a peak $t > 0$, the height-zero endpoints (`AxisFlow.axisEndpoint`) are the infimum of the lower endpoints and the supremum of the upper endpoints of the arches with peak $t$ over base heights in $(0, t)$; $t$ is a transverse peak (`AxisFlow.transversePeaks`) when they lie strictly on either side of $P_a(0)$. `AxisFlow.axisWidths a` is the set of half-widths of the height-zero arches over transverse peaks, and for such a half-width $r$, `AxisFlow.axisM a r` is the height-zero midpoint (the average of the two height-zero endpoints minus $P_a(0)$). `ScaledProfile.reflectX a` is the coefficient vector of $P_a(-x)$, which describes the left half-plane. `AxisFlow.matchingDelta a b r` is `axisM a r - axisM b r` and `AxisFlow.matchingDomain a b` is `axisWidths a ∩ axisWidths b`. A point $x$ is an isolated zero of $f$ on $J$ (`IsIsolatedZeroOn f J x`) when $x \in J$, $f(x) = 0$, and some interval $(x - \varepsilon, x + \varepsilon)$ contains no other zero of $f$ in $J$.
--
--   **The height-zero fit.** For $r \in$ `axisWidths a`, `AxisFlow.axisLambda a r` is the slope $d$ of the quadratic profile fitted (as above) to the height-zero midpoint $M_a(r)$ = `axisM a r` and its derivative $M_a'(r)$ (`AxisFlow.axisV`).
--
--   **The statement.** Let $a \in \mathbb R^6$ and $d \in \mathbb R$ satisfy
--   $$u\,\varphi_a''(u) - \varphi_a'(u) + d < 0 \quad\text{for all } u > 0, \qquad \varphi_a'(u) \to +\infty \text{ as } u \to 0^+.$$
--   Then for every $r \in$ `axisWidths a`,
--   $$d < \texttt{axisLambda}\ a\ r.$$
--
--   Lean: `OAI.QuinticLienard.AxisFlow.axisLambda_gt`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/AxisReflection.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, cf. Proposition 5.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/AxisReflection.lean (declaration OAI.QuinticLienard.AxisFlow.axisLambda_gt)

import Mathlib
import Definitions.Def_OAIQWQL000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScaledProfile ScalarArcs
lemma axisLambda_gt {a : Fin 6 → ℝ} {r d : ℝ} (hr : r ∈ axisWidths a)
    (hp : ∀ u,0<u → u*curvature a u-slope a u+d<0)
    (hs : Tendsto (slope a) (𝓝[>] 0) atTop) : d<axisLambda a r := by
  sorry
end QuinticLienard.AxisFlow

end OAI
end
