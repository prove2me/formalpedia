-- Prove2me | Theorems.Thm_OAI_QuinticLienard_ActualCharacteristic_fitted_slope_lt
-- name    : OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:11:48.963978+00:00
-- url     : https://prove2.me/theorems/5db07e7e-24b7-4785-b52f-69abf0dda403
-- title:
--   If the quintic profile has positive third derivative, the fitted slope of an arch is below the profile slope at its base (OpenAI quintic Liénard)
-- statement:
--   **Notation** (definitions bundle `OAIQWQL000` of this split; the paper's Sections 2–3). For $a \in \mathbb R^6$ let $P_a(x) = \sum_{i=0}^{5} a_i x^i$ (`ScaledProfile.poly a`) and, on the right half-plane in the coordinate $u = x^2/2$, let $\varphi_a(u) = P_a(\sqrt{2u})$ be the profile (`QuinticProfile.profile a`). The bundle's formulas give $\varphi_a'(u)$ = `ScaledProfile.slope a u`, $\varphi_a''(u)$ = `ScaledProfile.curvature a u` and $\varphi_a'''(u)$ = `ScaledProfile.third a u` for $u > 0$. An arch of a profile $\varphi$ with base height $h$ and peak height $t > h$ is a solution of $du/dy = \varphi(u) - y$ that rises from $u = h$ to the peak $u(\varphi(t)) = t$ and returns to $h$ (`ScalarArcs.IsArch`); its half-width $r$ is half the distance between its two endpoints $y_<, y_>$, and its midpoint is $M = (y_< + y_>)/2 - \varphi(h)$.
--
--   **The quadratic fit** (the paper's Theorem 3.6). For a profile and a base height $h > 0$, let $M(h, r)$ be the midpoint of the arch with base $h$ and half-width $r$ (`PositiveWidth.midpointAtWidth`, the peak chosen with that width) and $M_r$ its derivative in $r$. The fitted slope $\lambda(h, r)$ and curvature $\kappa(h, r)$ (`QuinticFit.lambda a (h, r)`, `QuinticFit.kappa a (h, r)` for the profile $\varphi_a$) are the parameters $(d, k)$ of the quadratic profile $du + ku^2/2$ whose arch of half-width $r$ has the same midpoint $M$ and the same $r$-derivative $M_r$ (`QuadraticFit.fitD`, `QuadraticFit.fitK`; they are set to $0$ where no such parameters exist).
--
--   **Arches at a given width.** For a peak height $t$ and a half-width $r$, `ActualCharacteristic.Adm a t r` says that some base height $h \in (0, t)$ gives the arch of $\varphi_a$ with peak $t$ the half-width $r$; `ActualCharacteristic.point a t r` is $(b, r)$ with $b$ such a base height (chosen), and `ActualCharacteristic.k a t r` is the profile slope $\varphi_a'(b)$ there.
--
--   **The statement.** Let $a \in \mathbb R^6$ with $\varphi_a'''(h) > 0$ for all $h > 0$, and let $t, r$ satisfy `Adm a t r`. Then the fitted slope at the base is below the profile slope:
--   $$\lambda(b, r) < \varphi_a'(b).$$
--
--   Lean: `OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt`, OpenAI's theorem of that name (in `lean/OAI/Analysis/LienardCycles/ActualSlopeComparison.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, cf. Proposition 5.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/ActualSlopeComparison.lean (declaration OAI.QuinticLienard.ActualCharacteristic.fitted_slope_lt)

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
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates

theorem fitted_slope_lt {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) :
    QuinticFit.lambda a (point a t r)<k a t r := by
  sorry
end QuinticLienard.ActualCharacteristic

end OAI
end
