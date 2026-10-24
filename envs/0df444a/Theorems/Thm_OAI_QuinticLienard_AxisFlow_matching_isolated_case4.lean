-- Prove2me | Theorems.Thm_OAI_QuinticLienard_AxisFlow_matching_isolated_case4
-- name    : OAI.QuinticLienard.AxisFlow.matching_isolated_case4
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:12:52.666975+00:00
-- url     : https://prove2.me/theorems/83d40308-96e4-4488-a7f0-673d3fe98dcb
-- title:
--   If a₁ < 0, a₃ < 0 and a₅ ≥ 0, the height-zero matching function of a quintic profile has at most two isolated zeros (OpenAI quintic Liénard)
-- statement:
--   **Notation** (definitions bundle `OAIQWQL000` of this split; the paper's Sections 2–3). For $a \in \mathbb R^6$ let $P_a(x) = \sum_{i=0}^{5} a_i x^i$ (`ScaledProfile.poly a`) and, on the right half-plane in the coordinate $u = x^2/2$, let $\varphi_a(u) = P_a(\sqrt{2u})$ be the profile (`QuinticProfile.profile a`). The bundle's formulas give $\varphi_a'(u)$ = `ScaledProfile.slope a u`, $\varphi_a''(u)$ = `ScaledProfile.curvature a u` and $\varphi_a'''(u)$ = `ScaledProfile.third a u` for $u > 0$. An arch of a profile $\varphi$ with base height $h$ and peak height $t > h$ is a solution of $du/dy = \varphi(u) - y$ that rises from $u = h$ to the peak $u(\varphi(t)) = t$ and returns to $h$ (`ScalarArcs.IsArch`); its half-width $r$ is half the distance between its two endpoints $y_<, y_>$, and its midpoint is $M = (y_< + y_>)/2 - \varphi(h)$.
--
--   **Height zero.** For a peak $t > 0$, the height-zero endpoints (`AxisFlow.axisEndpoint`) are the infimum of the lower endpoints and the supremum of the upper endpoints of the arches with peak $t$ over base heights in $(0, t)$; $t$ is a transverse peak (`AxisFlow.transversePeaks`) when they lie strictly on either side of $P_a(0)$. `AxisFlow.axisWidths a` is the set of half-widths of the height-zero arches over transverse peaks, and for such a half-width $r$, `AxisFlow.axisM a r` is the height-zero midpoint (the average of the two height-zero endpoints minus $P_a(0)$). `ScaledProfile.reflectX a` is the coefficient vector of $P_a(-x)$, which describes the left half-plane. `AxisFlow.matchingDelta a b r` is `axisM a r - axisM b r` and `AxisFlow.matchingDomain a b` is `axisWidths a ∩ axisWidths b`. A point $x$ is an isolated zero of $f$ on $J$ (`IsIsolatedZeroOn f J x`) when $x \in J$, $f(x) = 0$, and some interval $(x - \varepsilon, x + \varepsilon)$ contains no other zero of $f$ in $J$.
--
--   **The statement.** Let $a \in \mathbb R^6$ with $a_1 < 0$, $a_3 < 0$ and $a_5 \ge 0$, and let $a^-$ = `reflectX a`. Then the set of isolated zeros of $r \mapsto M_a(r) - M_{a^-}(r)$, where $M_a$ = `axisM a`, on the set of half-widths common to both profiles has extended cardinality at most $2$:
--   $$\#\{r : r \text{ is an isolated zero of } \texttt{matchingDelta}\ a\ a^- \text{ on } \texttt{matchingDomain}\ a\ a^-\} \le 2.$$
--   The proof of `OAI.QuinticLienard.upper_bound` uses it through `limitCycle_encard_le_matching`, which bounds the number of limit cycles of the system with primitive $P_a$ by the number of these isolated zeros (the paper's Proposition 2.5).
--
--   Lean: `OAI.QuinticLienard.AxisFlow.matching_isolated_case4`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/AxisCases.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, Section 6; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/AxisCases.lean (declaration OAI.QuinticLienard.AxisFlow.matching_isolated_case4)

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
open ScaledProfile RealAnalysis
lemma matching_isolated_case4 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : a 3<0) (h5 : 0≤a 5) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard≤2 := by
  sorry
end QuinticLienard.AxisFlow

end OAI
end
