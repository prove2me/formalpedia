-- Prove2me | Theorems.Thm_OAI_QuinticLienard_ActualCharacteristic_feed_nonneg
-- name    : OAI.QuinticLienard.ActualCharacteristic.feed_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T18:11:48.87807+00:00
-- url     : https://prove2.me/theorems/0805c85c-75b3-4d98-8b6f-28e0c39d26ae
-- title:
--   If the quintic profile has positive third derivative, the feed term of the fitted-curvature transport is nonnegative (OpenAI quintic Liénard)
-- statement:
--   **Notation** (definitions bundle `OAIQWQL000` of this split; the paper's Sections 2–3). For $a \in \mathbb R^6$ let $P_a(x) = \sum_{i=0}^{5} a_i x^i$ (`ScaledProfile.poly a`) and, on the right half-plane in the coordinate $u = x^2/2$, let $\varphi_a(u) = P_a(\sqrt{2u})$ be the profile (`QuinticProfile.profile a`). The bundle's formulas give $\varphi_a'(u)$ = `ScaledProfile.slope a u`, $\varphi_a''(u)$ = `ScaledProfile.curvature a u` and $\varphi_a'''(u)$ = `ScaledProfile.third a u` for $u > 0$. An arch of a profile $\varphi$ with base height $h$ and peak height $t > h$ is a solution of $du/dy = \varphi(u) - y$ that rises from $u = h$ to the peak $u(\varphi(t)) = t$ and returns to $h$ (`ScalarArcs.IsArch`); its half-width $r$ is half the distance between its two endpoints $y_<, y_>$, and its midpoint is $M = (y_< + y_>)/2 - \varphi(h)$.
--
--   **The quadratic fit** (the paper's Theorem 3.6). For a profile and a base height $h > 0$, let $M(h, r)$ be the midpoint of the arch with base $h$ and half-width $r$ (`PositiveWidth.midpointAtWidth`, the peak chosen with that width) and $M_r$ its derivative in $r$. The fitted slope $\lambda(h, r)$ and curvature $\kappa(h, r)$ (`QuinticFit.lambda a (h, r)`, `QuinticFit.kappa a (h, r)` for the profile $\varphi_a$) are the parameters $(d, k)$ of the quadratic profile $du + ku^2/2$ whose arch of half-width $r$ has the same midpoint $M$ and the same $r$-derivative $M_r$ (`QuadraticFit.fitD`, `QuadraticFit.fitK`; they are set to $0$ where no such parameters exist).
--
--   **Arches at a given width.** For a peak height $t$ and a half-width $r$, `ActualCharacteristic.Adm a t r` says that some base height $h \in (0, t)$ gives the arch of $\varphi_a$ with peak $t$ the half-width $r$; `ActualCharacteristic.point a t r` is $(b, r)$ with $b$ such a base height (chosen). Let $m$ be the midpoint of the arch with base $b$ and half-width $r$ (`PositiveWidth.midpointAtWidth`) and $g = r^2 - m^2$ (`ActualCharacteristic.g`). The feed term (`ActualCharacteristic.feed a t r`) is
--   $$\frac{g}{r}\; C_r\bigl(\lambda(b, r), \kappa(b, r), r\bigr)\;\bigl(\lambda(b, r) - \varphi_a'(b)\bigr),$$
--   where $C_r$ = `QuadraticCoordinates.Cr` is the $r$-derivative of the quadratic-model coefficient `QuadraticCoordinates.C`.
--
--   **The statement.** Let $a \in \mathbb R^6$ with $\varphi_a'''(h) > 0$ for all $h > 0$, and let $t, r$ satisfy `Adm a t r`. Then the feed term is nonnegative:
--   $$0 \le \texttt{feed}\ a\ t\ r.$$
--
--   Lean: `OAI.QuinticLienard.ActualCharacteristic.feed_nonneg`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LienardCycles/CurvaturePositive.lean`).
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf, cf. Proposition 5.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LienardCycles/CurvaturePositive.lean (declaration OAI.QuinticLienard.ActualCharacteristic.feed_nonneg)

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
lemma feed_nonneg {a : Fin 6 → ℝ} {t r : ℝ} (he : Adm a t r)
    (hthird : ∀ h, 0<h → 0<ScaledProfile.third a h) : 0≤feed a t r := by
  sorry
end QuinticLienard.ActualCharacteristic

end OAI
end
