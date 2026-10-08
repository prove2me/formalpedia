-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_4_2
-- name    : LogGammaPolymer.Variance.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:14.205974+00:00
-- url     : https://prove2.me/theorems/d85d7db8-373f-4393-9eb8-bd3b9d198c7d
-- title:
--   Lemma 4.2 — E[Σ_{i≤ξ_x} L(θ, Y_{i,0}^{-1})] ≤ C(E(ξ_x) + 1)
-- statement:
--   Assume (2.4) with $0<\theta<\mu$. There exists a constant $0<C<\infty$, depending only on $\theta$ and $\mu$, such that for all $m,n$
--   $$E\Bigl[\sum_{i=1}^{\xi_x}L(\theta,Y_{i,0}^{-1})\Bigr]\le C\bigl(E(\xi_x)+1\bigr)\qquad(4.24),$$
--   where $E=E_{m,n}$ is the annealed expectation.
--
--   Together with (3.18) this reduces the upper bound on $\mathrm{Var}[\log Z_{m,n}]$ to an upper bound on the annealed mean exit point $E(\xi_x)$.
--
--   **Formalization Note** The constant is chosen before $m$, $n$ and the environment. Integrability of the quenched average on the left is part of the conclusion, so that the bound cannot hold through the Bochner integral's junk value $0$.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 4.2, (4.24), p. 23

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_4_2 {θ μ : ℝ} (hθ : 0 < θ) (hθμ : θ < μ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (E : Env θ μ P) (m n : ℕ),
      Integrable (quenchedMean E m n
        (fun x ω => ∑ i ∈ Finset.Icc 1 (ξx x.1), Lfun θ (E.Y (i, 0) ω)⁻¹)) P ∧
      Eann E m n (fun x ω => ∑ i ∈ Finset.Icc 1 (ξx x.1), Lfun θ (E.Y (i, 0) ω)⁻¹) ≤
        C * (Eann E m n (fun x _ => (ξx x.1 : ℝ)) + 1) := by sorry

end LogGammaPolymer.Variance
