-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_variance_5_9
-- name    : MeanFieldDNN.TwoLayer.variance_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:54.457662+00:00
-- url     : https://prove2.me/theorems/fd23da7f-3ff2-478c-a3c0-b52b0c485ee0
-- title:
--   Equation (5.9) — variance of the empirical limiting output
-- statement:
--   Fix a solution of (2.6). For independent $c_1,\ldots,c_{N_2}$ with law $\mu_c$, set $f_t(c,x)=\widetilde C_t^c\widetilde H_t^{2,c}(x)$ and $g_t(x)=\int f_t(c,x)\,\mu_c(dc)$. A constant $K$ independent of $N_2$, $t\in[0,1]$, and $x\in X$ satisfies
--
--   $$\mathbb E\left[\left(\frac1{N_2}\sum_i f_t(c_i,x)-g_t(x)\right)^2\right]\le\frac K{N_2}.$$
--
--   This controls the sampling fluctuation of the limiting output in the second-width argument.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 22, (5.9)

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem variance_5_9 {d : ℕ} (S : Setting d) (L : LimitPaths d)
    (hL : IsLimitSolution S L) :
    ∃ K : ℝ, ∀ (N2 : ℕ), 1 ≤ N2 → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ S.X,
        (∫ cv : Fin N2 → ℝ,
          (((1 / (N2 : ℝ)) * ∑ i : Fin N2,
              L.Ct t (cv i) * limH2 S L t (cv i) x) - limG S L t x) ^ 2
          ∂(Measure.pi fun _ : Fin N2 => S.μc)) ≤ K / (N2 : ℝ) := by sorry
end MeanFieldDNN.TwoLayer
