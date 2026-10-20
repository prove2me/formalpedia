-- Prove2me | Theorems.Thm_NonconcaveUtil_Viscosity_theorem_4_1
-- name    : NonconcaveUtil.Viscosity.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:49.840088+00:00
-- url     : https://prove2.me/theorems/61e2da85-328c-4911-aac6-a06fe7550b18
-- title:
--   Theorem 4.1 — comparison principle for the portfolio HJB equation
-- statement:
--   Let $\bar v$ be a viscosity subsolution and $\underline v$ a viscosity supersolution of the portfolio Hamilton–Jacobi–Bellman equation, with the liquidation boundary condition and the appropriate terminal asymptotic condition. Suppose both lie below the same bound $C_1w^{\hat p}+C_2$ for positive $C_1,C_2$. Then
--
--   $$\bar v(t,w)\le\underline v(t,w)\qquad(0<t<T,\ w>B).$$
--
--   This comparison principle is the uniqueness step for the paper's solution concept, including a discontinuous utility at maturity.
--
--   **Formalization Note** The statement uses the one-stock data and Assumption 3.1. It compares values on the interior $w>B$; Definition A.1 does not prescribe a value of either arbitrary candidate at $w=B$.
-- source:
--   Dai, Kou, Qian & Wan, Nonconcave utility maximization with portfolio bounds, accepted manuscript (Management Science 68(11), 2022; DOI 10.1287/mnsc.2021.4228), p. 12 (PDF 12), Theorem 4.1

import Mathlib
import Definitions.Def_NonconcaveUtil_Viscosity_Solution

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NonconcaveUtil.Viscosity

/-- Theorem 4.1, p. 12: comparison in the growth class of Assumption 3.1. -/
theorem theorem_4_1 (mk : Market) (hmk : mk.Standing) (U : ℝ → ℝ)
    (pHat : ℝ) (bc : BdryCase) (hU : Assumption31 mk U pHat bc)
    (v₁ v₂ : ℝ → ℝ → ℝ)
    (hsub : IsViscositySubsolution mk U bc v₁)
    (hsuper : IsViscositySupersolution mk U bc v₂)
    (hgrowth : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ q ∈ mk.D, v₁ q.1 q.2 ≤ C₁ * q.2 ^ pHat + C₂ ∧
        v₂ q.1 q.2 ≤ C₁ * q.2 ^ pHat + C₂) :
    ∀ t ∈ Set.Ioo 0 mk.T, ∀ w > mk.B, v₁ t w ≤ v₂ t w := by sorry

end NonconcaveUtil.Viscosity
