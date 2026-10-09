-- Prove2me | Theorems.Thm_InventoryBounds_two_point_estimation_information
-- name    : InventoryBounds.two_point_estimation_information
-- status  : Open
-- author  : @visuddhi
-- created : 2026-10-08T15:34:06.597223+00:00
-- url     : https://prove2.me/theorems/40199c55-fb5f-4b40-b533-936498196b5f
-- title:
--   Theorem 3.7 — randomized estimation-to-testing information bound
-- statement:
--   Consider M IID zero/unit observations with zero probabilities rho0 or rho1, both strictly between zero and one. The same arbitrary Markov kernel maps the archive to a randomized real estimate. If it lies within epsilon of v0 or v1 with probability at least 1-eta respectively, where v1-v0>2epsilon and 0<eta<1/2, then M kl(rho1,rho0) is at least (1-2eta) log((1-eta)/eta).
-- source:
--   Hanzhang Qin, David Simchi-Levi, Ruihao Zhu, Information Limits of Multistage Inventory Control: Learning, Valuation, and Censoring, arXiv:2609.37380v1 (29 September 2026), https://arxiv.org/abs/2609.37380v1, Theorem 3.7, testing and data-processing step

import Definitions.Def_InventoryBounds_StationaryValuation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InventoryBounds

theorem two_point_estimation_information (M : ℕ)
    (κ : Kernel (Fin M → Bool) ℝ) [IsMarkovKernel κ]
    (ρ₀ ρ₁ v₀ v₁ ε η : ℝ)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hε : 0 < ε) (hη : 0 < η) (hη2 : η < 1 / 2)
    (hsep : 2 * ε < v₁ - v₀)
    (hs₀ : 1 - η ≤ estimatorSuccess κ ρ₀ v₀ ε)
    (hs₁ : 1 - η ≤ estimatorSuccess κ ρ₁ v₁ ε) :
    (1 - 2 * η) * Real.log ((1 - η) / η) ≤ (M : ℝ) * binaryKL ρ₁ ρ₀ := by sorry

end InventoryBounds
