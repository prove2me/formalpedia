-- Prove2me | Theorems.Thm_HighEntropyLimit_pure_stretch_entropy_increase
-- name    : HighEntropyLimit.pure_stretch_entropy_increase
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:58:11.466091+00:00
-- url     : https://prove2.me/theorems/a5374461-312c-4fb9-b6f8-d3697741ca48
-- title:
--   A pure stretch increases Gibbs entropy by $\log\lambda$
-- statement:
--   Let $\lambda>1$ and let $\rho$ be a probability density on phase space $\mathbb R^2$ with finite entropy: $\rho\ge0$, $\int\rho = 1$, and $\rho$, $\rho\log\rho$ integrable. Let $T\rho(z) = \lambda^{-1}\rho(z/\sqrt\lambda)$ be its image under the pure stretching map $T(x,p) = (\sqrt\lambda x, \sqrt\lambda p)$. Then
--   $$S(T\rho) = S(\rho) + \log\lambda, \qquad S(\rho) = -\int\rho\log\rho\,dx\,dp.$$
--
--   **Formalization Note** The integrability of $\rho\log\rho$ (finite entropy) is implicit in the paper.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 7, Eq. (15) (requirement S(R(ρ)) = S(ρ) + log λ) for the pure stretching map of Eq. (16)

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch
open MeasureTheory

namespace HighEntropyLimit
theorem pure_stretch_entropy_increase (lam : ℝ) (hlam : 1 < lam) (ρ : ℝ × ℝ → ℝ)
    (hρ_nonneg : ∀ z, 0 ≤ ρ z) (hρ_int : Integrable ρ) (hρ_norm : ∫ z, ρ z = 1)
    (hρ_ent : Integrable (fun z => ρ z * Real.log (ρ z))) :
    gibbsEntropy (pureStretch lam ρ) = gibbsEntropy ρ + Real.log lam := by sorry
end HighEntropyLimit
