-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_theorem_3_7
-- name    : LogGammaPolymer.Variance.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:12.337985+00:00
-- url     : https://prove2.me/theorems/c911d826-9c30-40a6-a5ac-b5f796d5bf57
-- title:
--   Theorem 3.7 — variance of log Z_{m,n} in terms of the exit points ξ_x, ξ_y, (3.18)–(3.19)
-- statement:
--   Assume (2.4) with $0<\theta<\mu$. Then for $m,n\in\mathbb Z_+$, $\log Z_{m,n}$ has a finite second moment and
--   $$\mathrm{Var}\bigl[\log Z_{m,n}\bigr]=n\Psi_1(\mu-\theta)-m\Psi_1(\theta)+2\,E_{m,n}\Bigl[\sum_{i=1}^{\xi_x}L(\theta,Y_{i,0}^{-1})\Bigr]\qquad(3.18)$$
--   and
--   $$\mathrm{Var}\bigl[\log Z_{m,n}\bigr]=-n\Psi_1(\mu-\theta)+m\Psi_1(\theta)+2\,E_{m,n}\Bigl[\sum_{j=1}^{\xi_y}L(\mu-\theta,Y_{0,j}^{-1})\Bigr]\qquad(3.19).$$
--   Here $E_{m,n}$ is the annealed expectation, $L$ is the function (3.17), and an empty sum ($\xi_x=0$ or $\xi_y=0$) is $0$.
--
--   These identities convert the variance of the free energy into the annealed size of the exit points of the polymer path from the axes. Both bounds of Theorem 2.1 go through them.
--
--   **Formalization Note** The conclusion also asserts `MemLp (log Z) 2` and integrability of the quenched averages, so that neither Mathlib's `variance` (which is $0$ for an infinite second moment) nor the Bochner integral can satisfy the identities by a junk value.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Theorem 3.7, (3.18)–(3.19), p. 15

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem theorem_3_7 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (E : Env θ μ P) (m n : ℕ) :
    MemLp (logZ E m n) 2 P ∧
    Integrable (quenchedMean E m n
      (fun x ω => ∑ i ∈ Finset.Icc 1 (ξx x.1), Lfun θ (E.Y (i, 0) ω)⁻¹)) P ∧
    variance (logZ E m n) P = n * Psi1 (μ - θ) - m * Psi1 θ +
      2 * Eann E m n (fun x ω => ∑ i ∈ Finset.Icc 1 (ξx x.1), Lfun θ (E.Y (i, 0) ω)⁻¹) ∧
    Integrable (quenchedMean E m n
      (fun x ω => ∑ j ∈ Finset.Icc 1 (ξy x.1), Lfun (μ - θ) (E.Y (0, j) ω)⁻¹)) P ∧
    variance (logZ E m n) P = -(n * Psi1 (μ - θ)) + m * Psi1 θ +
      2 * Eann E m n (fun x ω => ∑ j ∈ Finset.Icc 1 (ξy x.1), Lfun (μ - θ) (E.Y (0, j) ω)⁻¹) := by sorry

end LogGammaPolymer.Variance
