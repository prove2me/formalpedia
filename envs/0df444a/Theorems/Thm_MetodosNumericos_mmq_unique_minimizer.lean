-- Prove2me | Theorems.Thm_MetodosNumericos_mmq_unique_minimizer
-- name    : MetodosNumericos.mmq_unique_minimizer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:05:02.141664+00:00
-- url     : https://prove2.me/theorems/a1f4d14f-aa7f-4757-a093-ceb09cf4f8a5
-- title:
--   Existence and uniqueness of the fit when the Gram matrix is invertible
-- statement:
--   If the Gram matrix $a_{kj} = \\sum_i \\varphi_k(x_i)\\varphi_j(x_i)$ has nonzero determinant, then there is exactly one coefficient vector minimizing the sum of squared residuals. This supplies the hypothesis under which the source's assumption that $S$ attains a minimum is justified.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 6, §6.3, p. 122 ("Vamos supor que a função S tenha um ponto de mínimo").

import Mathlib
import Definitions.Def_MetodosNumericos_ajusteDefs

namespace MetodosNumericos

theorem mmq_unique_minimizer {m n : ℕ} (phi : Fin (n + 1) → ℝ → ℝ)
    (x f : Fin (m + 1) → ℝ) (hgram : IsUnit (gramMatrix phi x).det) :
    ∃! c : Fin (n + 1) → ℝ, ∀ d : Fin (n + 1) → ℝ, sqError phi x f c ≤ sqError phi x f d := by
  sorry

end MetodosNumericos
