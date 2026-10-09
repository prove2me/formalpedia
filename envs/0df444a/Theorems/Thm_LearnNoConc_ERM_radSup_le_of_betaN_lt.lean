-- Prove2me | Theorems.Thm_LearnNoConc_ERM_radSup_le_of_betaN_lt
-- name    : LearnNoConc.ERM.radSup_le_of_betaN_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:49:54.03982+00:00
-- url     : https://prove2.me/theorems/71e959f9-6c46-4ea1-81d6-e79dd4bbcf72
-- title:
--   §5, p. 20 — star-shaped H and r > β_N(γ) ⇒ E sup_{h∈H∩rD} |N⁻¹Σε_ih(X_i)| ≤ γr
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N\ge1$, $\gamma>0$, and let $H$ be a class of real functions on $\Omega$ that is star-shaped around $0$ (if $h\in H$ and $0<\lambda\le1$ then $\lambda h\in H$). Let $X_1,\dots,X_N$ be i.i.d. with law $\mu$ and $(\varepsilon_i)$ independent random signs. If $r>\beta_N(H,\gamma)$, then
--
--   $$\mathbb E\sup_{h\in H\cap rD}\Bigl|\frac1N\sum_{i=1}^N\varepsilon_i h(X_i)\Bigr|\le\gamma r,$$
--
--   where $D$ is the unit ball of $L_2(\mu)$.
--
--   The infimum $\beta_N(H,\gamma)$ need not be attained; this statement says that for a star-shaped class the defining inequality holds at every radius above it. It is the localization step used in Corollary 5.5.
--
--   **Formalization Note** The expectation of the supremum is taken in $[0,\infty]$ (Mathlib's lower Lebesgue integral), and $\beta_N$ is $[0,\infty]$-valued; no measurability hypothesis is needed for this statement.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, §5, p. 20, "it is straightforward to verify that if H is star-shaped"

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- §5, p. 20: if `H` is star-shaped around `0` and `r > β_N(H, γ)`, then
`E sup_{h ∈ H ∩ rD} |(1/N) ∑ ε_i h(X_i)| ≤ γ r`. -/
theorem radSup_le_of_betaN_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (H : Set (Ω → ℝ)) (hH : StarShaped H) (N : ℕ) (hN : 0 < N)
    (γ : ℝ) (hγ : 0 < γ) (r : ℝ) (hr : betaN μ H N γ < ENNReal.ofReal r) :
    radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N ≤ ENNReal.ofReal (γ * r) := by sorry

end LearnNoConc.ERM
