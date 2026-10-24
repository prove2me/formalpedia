-- Prove2me | Theorems.Thm_OAI_QuinticLienard_AxisFlow_kappa_antitone_height
-- name    : OAI.QuinticLienard.AxisFlow.kappa_antitone_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:12:20.366791+00:00
-- url     : https://prove2.me/theorems/62939fa8-cfad-4a4a-984e-b1b58b0e5660
-- title:
--   If the quintic profile has negative third derivative, the fitted curvature is nonincreasing in the width at each base height (OpenAI quintic Liénard, cf. Proposition 5.2)
-- statement:
--   **Notation** (definitions bundle `OAIQWQL000` of this split; the paper's Sections 2–3). For $a \in \mathbb R^6$ let $P_a(x) = \sum_{i=0}^{5} a_i x^i$ (`ScaledProfile.poly a`) and, on the right half-plane in the coordinate $u = x^2/2$, let $\varphi_a(u) = P_a(\sqrt{2u})$ be the profile (`QuinticProfile.profile a`). The bundle's formulas give $\varphi_a'(u)$ = `ScaledProfile.slope a u`, $\varphi_a''(u)$ = `ScaledProfile.curvature a u` and $\varphi_a'''(u)$ = `ScaledProfile.third a u` for $u > 0$. An arch of a profile $\varphi$ with base height $h$ and peak height $t > h$ is a solution of $du/dy = \varphi(u) - y$ that rises from $u = h$ to the peak $u(\varphi(t)) = t$ and returns to $h$ (`ScalarArcs.IsArch`); its half-width $r$ is half the distance between its two endpoints $y_<, y_>$, and its midpoint is $M = (y_< + y_>)/2 - \varphi(h)$.
--
--   **The quadratic fit** (the paper's Theorem 3.6). For a profile and a base height $h > 0$, let $M(h, r)$ be the midpoint of the arch with base $h$ and half-width $r$ (`PositiveWidth.midpointAtWidth`, the peak chosen with that width) and $M_r$ its derivative in $r$. The fitted slope $\lambda(h, r)$ and curvature $\kappa(h, r)$ (`QuinticFit.lambda a (h, r)`, `QuinticFit.kappa a (h, r)` for the profile $\varphi_a$) are the parameters $(d, k)$ of the quadratic profile $du + ku^2/2$ whose arch of half-width $r$ has the same midpoint $M$ and the same $r$-derivative $M_r$ (`QuadraticFit.fitD`, `QuadraticFit.fitK`; they are set to $0$ where no such parameters exist).
--
--   **The statement.** Let $a \in \mathbb R^6$ with $\varphi_a'''(u) < 0$ for all $u > 0$, and let $h > 0$. Then the fitted curvature at base height $h$ is antitone in the half-width:
--   $$r \mapsto \kappa(h, r) \text{ is nonincreasing on } (0, \infty).$$
--
--   Lean: `OAI.QuinticLienard.AxisFlow.kappa_antitone_height`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/AxisComparison.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, cf. Proposition 5.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/AxisComparison.lean (declaration OAI.QuinticLienard.AxisFlow.kappa_antitone_height)

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
open ScaledProfile PositiveWidth PartialCalculus
lemma kappa_antitone_height {a : Fin 6 → ℝ} {h : ℝ} (hh : 0<h)
    (hp : ∀ u,0<u → third a u<0) : AntitoneOn (fun r=>QuinticFit.kappa a (h,r)) (Ioi 0) := by
  sorry
end QuinticLienard.AxisFlow

end OAI
end
