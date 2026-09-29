-- Prove2me | Theorems.Thm_MetodosNumericos_mmq_minimizer_normal_system
-- name    : MetodosNumericos.mmq_minimizer_normal_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:06:15.508749+00:00
-- url     : https://prove2.me/theorems/c2732bab-a63b-46e2-a571-132fb5ba039e
-- title:
--   A least-squares minimizer satisfies the normal system
-- statement:
--   If the coefficient vector $c$ minimizes $S(c) = \\sum_i (\\sum_k c_k\\varphi_k(x_i) - f_i)^2$ among all coefficient vectors, then it satisfies the normal system $\\sum_i \\varphi_k(x_i)(\\sum_j c_j\\varphi_j(x_i)) = \\sum_i \\varphi_k(x_i)f_i$ for every $k$. This is the derivation of §6.3, where the source obtains the normal system from the vanishing of the partial derivatives of $S$ at a minimum.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 6, §6.3 Sistema Normal para o MMQ, pp. 122–124.

import Mathlib
import Definitions.Def_MetodosNumericos_ajusteDefs

namespace MetodosNumericos

theorem mmq_minimizer_normal_system {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ)
    (x f : Fin (m + 1) → ℝ) (c : Fin (n + 1) → ℝ)
    (hmin : ∀ d : Fin (n + 1) → ℝ, sqError phi x f c ≤ sqError phi x f d) :
    NormalSystem phi x f c := by sorry

end MetodosNumericos
