-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_eq_2_5
-- name    : LogGammaPolymer.Variance.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:02.281451+00:00
-- url     : https://prove2.me/theorems/25409b5d-2da8-4177-89dc-e52f63921a49
-- title:
--   (2.5) — E[log Z_{m,n}] = mE(log U) + nE(log V) = −mΨ₀(θ) − nΨ₀(μ − θ)
-- statement:
--   Assume (2.4) with $0<\theta<\mu$. For all $m,n\ge0$ the free energy $\log Z_{m,n}$ is integrable and
--   $$\mathbb E\bigl[\log Z_{m,n}\bigr]=m\,\mathbb E(\log U)+n\,\mathbb E(\log V)=-m\Psi_0(\theta)-n\Psi_0(\mu-\theta),$$
--   where $U=U_{1,0}$ and $V=V_{0,1}$ are boundary weights.
--
--   The mean of the free energy is thus exactly linear in the endpoint, with no correction term; the fluctuations studied in the rest of the mission are fluctuations around this explicit line.
--
--   **Formalization Note** Integrability is part of the conclusion, so that the identity cannot hold through the Bochner integral's value $0$ on non-integrable functions.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, eq. (2.5), p. 6

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem eq_2_5 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (E : Env θ μ P) (m n : ℕ) :
    Integrable (logZ E m n) P ∧
    ∫ ω, logZ E m n ω ∂P =
      m * ∫ ω, Real.log (E.Y (1, 0) ω) ∂P + n * ∫ ω, Real.log (E.Y (0, 1) ω) ∂P ∧
    ∫ ω, logZ E m n ω ∂P = -(m * Psi0 θ) - n * Psi0 (μ - θ) := by sorry

end LogGammaPolymer.Variance
