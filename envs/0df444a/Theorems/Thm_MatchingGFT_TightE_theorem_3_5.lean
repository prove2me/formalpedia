-- Prove2me | Theorems.Thm_MatchingGFT_TightE_theorem_3_5
-- name    : MatchingGFT.TightE.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:47.075343+00:00
-- url     : https://prove2.me/theorems/2759e17c-66e7-49e6-8a34-b975d34a3829
-- title:
--   Theorem 3.5 — Local bound on GFT
-- statement:
--   For $Q_B$ nonincreasing and $Q_S$ nondecreasing, both integrable from $(0,1)$ to $[0,\infty)$, and a measurable down-set $\mathcal D\subseteq(0,1)^2$ with $Q_B(\rho)\ge Q_S(\sigma)$ a.e. on $\mathcal D$: $\int_{\mathcal D}(Q_B(\rho)-Q_S(\sigma))\,d\rho\,d\sigma\le\frac e2(P_S(\mathcal D)+P_B(\mathcal D))$.
--
--   Differences from the source:
--   - encoding: quantile functions on (0,1) → functions ℝ → ℝ with hypotheses on (0,1); reason: only values on (0,1) enter
--   - encoding: the term at x = 0 (y = 0) is zero and an empty section contributes zero → threshold-profit objective is 0 at 0, and the real sSup of an empty range is 0; reason: same value; the range is bounded because Q_B is integrable and Q_S nonnegative
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Theorem 3.5, PDF p. 14; assumptions PDF p. 13

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Regions

open MeasureTheory Set

namespace MatchingGFT.TightE

/-- Theorem 3.5 (PDF p. 14, assumptions p. 13): for `Q_B` nonincreasing, `Q_S` nondecreasing, both
integrable `(0, 1) → [0, ∞)`, and a measurable down-set `D` of `(0, 1)²` with `Q_B(ρ) ≥ Q_S(σ)` a.e. on `D`,
`∫_D (Q_B(ρ) - Q_S(σ)) dρ dσ ≤ (e/2) (P_S(D) + P_B(D))`. -/
theorem theorem_3_5 (QB QS : ℝ → ℝ)
    (hQB0 : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ QB u) (hQS0 : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ QS u)
    (hQBanti : AntitoneOn QB (Ioo 0 1)) (hQSmono : MonotoneOn QS (Ioo 0 1))
    (hQBint : IntegrableOn QB (Ioo 0 1)) (hQSint : IntegrableOn QS (Ioo 0 1))
    (D : Set (ℝ × ℝ)) (hD : IsRankDownSet D)
    (hgft : ∀ᵐ p ∂(volume.restrict D), QS p.2 ≤ QB p.1) :
    ∫ p in D, (QB p.1 - QS p.2) ≤
      (Real.exp 1 / 2) * (benchmarkS QB QS D + benchmarkB QB QS D) := by sorry

end MatchingGFT.TightE
