-- Prove2me | Theorems.Thm_HooftDimReduction_thermal_gas_entropy_bound
-- name    : HooftDimReduction.thermal_gas_entropy_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T01:18:10.589111+00:00
-- url     : https://prove2.me/theorems/dfb7f82e-c56f-4744-9817-2473fe001c22
-- title:
--   Eqs. (4)–(8): a thermal gas outside its Schwarzschild radius has $S<C_4Z^{1/4}V^{1/2}=C_5Z^{1/4}A^{3/4}$
-- statement:
--   Let $C_1,C_2>0$ be constants. There are constants $C_3,C_4,C_5>0$, depending only on $C_1,C_2$, with the following property. Let $Z>0$ (number of particle species), $R>0$ (radius of a sphere with volume $V=\tfrac43\pi R^3$ and area $A=4\pi R^2$) and $T>0$ (temperature). Set $E=C_1ZVT^4$ and $S=C_2ZVT^3$ (eqs. (4), (5)). If the Schwarzschild condition $2E<R$ (eq. (6)) holds, then
--   $$T<C_3\,Z^{-1/4}V^{-1/6},\qquad S<C_4\,Z^{1/4}V^{1/2},\qquad S<C_5\,Z^{1/4}A^{3/4}.$$
--
--   This is the estimate showing that ordinary field-theoretic matter which does not collapse has entropy growing like $A^{3/4}$, much less than the black-hole value $A/4$ for large $A$.
--
--   **Formalization Note** The region is a round sphere, so eq. (6), $2E<(V/\tfrac43\pi)^{1/3}$, is written as $2E<R$. Real powers are `Real.rpow` with positive bases.
-- source:
--   G. 't Hooft, "Dimensional Reduction in Quantum Gravity", essay dedicated to Abdus Salam, Utrecht preprint THU-93/26, arXiv:gr-qc/9310026v2, https://arxiv.org/abs/gr-qc/9310026, p. 5, eqs. (4)–(8)

import Mathlib

namespace HooftDimReduction

theorem thermal_gas_entropy_bound (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₃ C₄ C₅ : ℝ, 0 < C₃ ∧ 0 < C₄ ∧ 0 < C₅ ∧
      ∀ Z R T : ℝ, 0 < Z → 0 < R → 0 < T →
        2 * (C₁ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 4) < R →
          T < C₃ * Z ^ (-(1 / 4 : ℝ)) * (4 / 3 * Real.pi * R ^ 3) ^ (-(1 / 6 : ℝ)) ∧
          C₂ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 3 <
            C₄ * Z ^ (1 / 4 : ℝ) * (4 / 3 * Real.pi * R ^ 3) ^ (1 / 2 : ℝ) ∧
          C₂ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 3 <
            C₅ * Z ^ (1 / 4 : ℝ) * (4 * Real.pi * R ^ 2) ^ (3 / 4 : ℝ) := by sorry

end HooftDimReduction
