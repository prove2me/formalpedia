-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_smooth_ae_eq_of_L2div_eq_zero
-- name    : MultivarScores.L2Rule.smooth_ae_eq_of_L2div_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:27.469735+00:00
-- url     : https://prove2.me/theorems/be9ad5af-ff26-4370-8967-0b863ed8adc7
-- title:
--   Proof of Theorem 1, p. 32 — if Δ = 0 and h ≠ 0 𝓛^d-a.e., then f_X ∗ w = f_Y ∗ w 𝓛^d-a.e.
-- statement:
--   Let $P_X,P_Y$ be distributions on $\mathbb R^d$, $w$ a kernel and $h\ge0$ a weight that is nonzero $\mathcal L^d$-almost everywhere. Suppose the function $\big((f_X*w)-(f_Y*w)\big)^2h$ is integrable. If
--
--   $$\int_{\mathbb R^d}\big((f_X*w)(z)-(f_Y*w)(z)\big)^2h(z)\,dz=0,$$
--
--   then $f_X*w=f_Y*w$ $\mathcal L^d$-almost everywhere.
--
--   This is the strict-properness step of the proof of Theorem 1: a vanishing divergence forces the smoothed densities to agree, after which the characterization property of $f_Y*w$ gives $P_X=P_Y$.
--
--   **Formalization Note** The integrability hypothesis is necessary in Lean: the Bochner integral of a non-integrable function is $0$, which would make the hypothesis "$=0$" hold for free. Under Assumption 1 it holds automatically.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 32, proof of Theorem 1, last paragraph

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- Strict-properness step in the proof of Theorem 1, p. 32: if `Δ = 0` and `h` is nonzero
`𝓛^d`-a.e., then `f_X ∗ w = f_Y ∗ w` `𝓛^d`-a.e. -/
theorem smooth_ae_eq_of_L2div_eq_zero {d : ℕ} (PX PY : Measure (E d)) (w h : E d → ℝ)
    (h_nonneg : ∀ z, 0 ≤ h z) (h_ne : ∀ᵐ z, h z ≠ 0)
    (hint : Integrable (fun z => (smooth PX w z - smooth PY w z) ^ 2 * h z))
    (h0 : L2div PX PY w h = 0) :
    smooth PX w =ᵐ[volume] smooth PY w := by sorry

end MultivarScores.L2Rule
