-- Prove2me | Theorems.Thm_MetodosNumericos_mmq_linear_case
-- name    : MetodosNumericos.mmq_linear_case
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:05:46.86534+00:00
-- url     : https://prove2.me/theorems/710f72d4-eee4-4158-a40b-79c5af748219
-- title:
--   The linear fit: the classical two-equation normal system
-- statement:
--   For the base functions $\\varphi_0 = 1$ and $\\varphi_1(t) = t$, a coefficient pair $(c_0,c_1)$ minimizes the sum of squared residuals if and only if $$c_0(m+1) + c_1\\sum_i x_i = \\sum_i f_i, \\qquad c_0\\sum_i x_i + c_1\\sum_i x_i^2 = \\sum_i x_i f_i,$$ the normal system of the straight-line fit of §6.1–6.3.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 6, §6.1 Caso Linear, pp. 119–124.

import Mathlib
import Definitions.Def_MetodosNumericos_ajusteDefs

namespace MetodosNumericos

theorem mmq_linear_case {m : ℕ} (x f : Fin (m + 1) → ℝ) (c : Fin 2 → ℝ)
    (phi : Fin 2 → ℝ → ℝ) (hphi0 : phi 0 = fun _ => 1) (hphi1 : phi 1 = fun t => t) :
    (∀ d : Fin 2 → ℝ, sqError phi x f c ≤ sqError phi x f d) ↔
      (c 0 * (m + 1 : ℝ) + c 1 * ∑ i : Fin (m + 1), x i = ∑ i : Fin (m + 1), f i ∧
        c 0 * (∑ i : Fin (m + 1), x i) + c 1 * ∑ i : Fin (m + 1), x i ^ 2 =
          ∑ i : Fin (m + 1), x i * f i) := by sorry

end MetodosNumericos
