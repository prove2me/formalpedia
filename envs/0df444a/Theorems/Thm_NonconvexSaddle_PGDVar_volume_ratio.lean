-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_volume_ratio
-- name    : NonconvexSaddle.PGDVar.volume_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:10:56.990217+00:00
-- url     : https://prove2.me/theorems/98affd50-6bc2-4c39-b9dc-eacd4b923f16
-- title:
--   §5, proof of Lemma 20, display on p. 15 — ratio of the volumes of the (d−1)- and d-dimensional balls
-- statement:
--   Let $d\ge1$, $a>0$ and $w>0$, and write $\mathbb B^k_0(a)$ for the Euclidean ball of radius $a$ around $0$ in $\mathbb R^k$ and $\mathrm{Vol}$ for Lebesgue measure. Then
--   $$\frac{w\cdot\mathrm{Vol}(\mathbb B^{d-1}_0(a))}{\mathrm{Vol}(\mathbb B^{d}_0(a))}=\frac{w}{a\sqrt\pi}\cdot\frac{\Gamma(\frac d2+1)}{\Gamma(\frac d2+\frac12)}\le\frac wa\sqrt{\frac d\pi}.$$
--
--   In the proof of Lemma 20 this is applied with $a=\eta r$ and $w=\eta\omega$: a measurable set of width at most $\eta\omega$ along one direction inside the perturbation ball has probability at most $\frac{\omega}{r}\sqrt{d/\pi}$ under the uniform law. This is how the stuck region of Lemma 22 is shown to be unlikely.
--
--   **Formalization Note** $\mathbb R^{d-1}$ is `EuclideanSpace ℝ (Fin (d - 1))`; for $d=1$ it is a point and $\mathrm{Vol}(\mathbb B^0_0(a))=1$. The volumes are real numbers (`ENNReal.toReal`), finite and positive for $a>0$. Only the purely geometric part of the display is stated; the first equality $\mathbb P(x_0\in\mathcal X_{\text{stuck}})=\mathrm{Vol}(\mathcal X_{\text{stuck}})/\mathrm{Vol}(\mathbb B^d_{\tilde x}(\eta r))$ and the final bound by $\ell\sqrt d\,\iota^22^{8-\iota}/\sqrt{\rho\varepsilon}$ belong to Lemma 20.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, §5, proof of Lemma 20, display on p. 15

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

namespace NonconvexSaddle.PGDVar

/-- The volume ratio of the proof of Lemma 20 (arXiv:1902.04811v2, §5, display on p. 15): for `d ≥ 1`,
a radius `a > 0` and a width `w > 0`,
`w · Vol(𝔹^{d−1}_0(a)) / Vol(𝔹^d_0(a)) = (w/(a√π)) · Γ(d/2 + 1)/Γ(d/2 + 1/2) ≤ (w/a)·√(d/π)`.
In the paper `a = ηr` and `w = ηω`. -/
theorem volume_ratio {d : ℕ} (hd : 1 ≤ d) (a w : ℝ) (ha : 0 < a) (hw : 0 < w) :
    w * (MeasureTheory.volume (Metric.ball (0 : NonconvexSaddle.PSGD.E (d - 1)) a)).toReal /
        (MeasureTheory.volume (Metric.ball (0 : NonconvexSaddle.PSGD.E d) a)).toReal =
      w / (a * Real.sqrt Real.pi) *
        (Real.Gamma ((d : ℝ) / 2 + 1) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) ∧
    w / (a * Real.sqrt Real.pi) *
        (Real.Gamma ((d : ℝ) / 2 + 1) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) ≤
      w / a * Real.sqrt ((d : ℝ) / Real.pi) := by sorry

end NonconvexSaddle.PGDVar
