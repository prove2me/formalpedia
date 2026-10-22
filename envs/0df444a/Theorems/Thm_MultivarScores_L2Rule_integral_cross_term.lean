-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_integral_cross_term
-- name    : MultivarScores.L2Rule.integral_cross_term
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:25.467743+00:00
-- url     : https://prove2.me/theorems/3a22b2f2-4272-4c66-89ba-580ff573991b
-- title:
--   Proof of Theorem 1, p. 32 — Fubini step: ∫∫ g(z) w(z − s) h(z) dz dP_Y(s) = ∫ g(z) (f_Y ∗ w)(z) h(z) dz
-- statement:
--   Let $P_Y$ be a probability distribution on $\mathbb R^d$ and let $g,w,h:\mathbb R^d\to\mathbb R$ be measurable. If $(s,z)\mapsto g(z)\,w(z-s)\,h(z)$ is integrable with respect to $P_Y\otimes\mathcal L^d$, then
--
--   $$\int_{\mathbb R^d}\Big(\int_{\mathbb R^d} g(z)\,w(z-s)\,h(z)\,dz\Big)\,dP_Y(s)=\int_{\mathbb R^d} g(z)\,(f_Y*w)(z)\,h(z)\,dz,$$
--
--   where $(f_Y*w)(z)=\int w(z-s)\,dP_Y(s)$.
--
--   This is the step of the proof of Theorem 1 that "holds by Fubini's theorem and the definition of convolution": it turns the expectation over the realization of the cross term of the expanded score into an integral against the smoothed density $f_Y*w$. With $g=f_X*w-f_Y*w$ it is the passage from the second to the third line of the divergence computation.
--
--   **Formalization Note** The product integrability is the form Assumption 1(c) takes for this cross term; it is what makes Fubini's theorem applicable.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 32, proof of Theorem 1, second and third lines of the divergence display

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- Fubini step in the proof of Theorem 1, p. 32: for a distribution `P_Y`,
`∫ (∫ g(z) w(z − s) h(z) dz) dP_Y(s) = ∫ g(z) (f_Y ∗ w)(z) h(z) dz`. -/
theorem integral_cross_term {d : ℕ} (PY : Measure (E d)) [IsProbabilityMeasure PY]
    (g w h : E d → ℝ) (hg : Measurable g) (hw : Measurable w) (hh : Measurable h)
    (hint : Integrable (fun p : E d × E d => g p.2 * w (p.2 - p.1) * h p.2) (PY.prod volume)) :
    ∫ s, (∫ z, g z * w (z - s) * h z) ∂PY = ∫ z, g z * smooth PY w z * h z := by sorry

end MultivarScores.L2Rule
