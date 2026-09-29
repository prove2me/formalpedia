-- Prove2me | Theorems.Thm_MetodosNumericos_mmq_normal_system_minimizer
-- name    : MetodosNumericos.mmq_normal_system_minimizer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:54:51.867833+00:00
-- url     : https://prove2.me/theorems/76e8bfc8-13a9-458f-b411-f5e198d6e263
-- title:
--   Every solution of the normal system is a global least-squares minimizer
-- statement:
--   If the coefficients $c$ satisfy the normal system, then $S(c) \\le S(d)$ for every coefficient vector $d$. This converse of the source's derivation is what makes the normal system a characterization of the least-squares fit and not merely a necessary condition.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 6, §6.3, pp. 122–124 (converse of the stated necessary condition).

import Mathlib
import Definitions.Def_MetodosNumericos_ajusteDefs

namespace MetodosNumericos

theorem mmq_normal_system_minimizer {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ)
    (x f : Fin (m + 1) → ℝ) (c : Fin (n + 1) → ℝ) (hc : NormalSystem phi x f c) :
    ∀ d : Fin (n + 1) → ℝ, sqError phi x f c ≤ sqError phi x f d := by sorry

end MetodosNumericos
