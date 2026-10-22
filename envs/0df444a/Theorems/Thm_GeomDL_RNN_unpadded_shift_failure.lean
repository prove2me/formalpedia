-- Prove2me | Theorems.Thm_GeomDL_RNN_unpadded_shift_failure
-- name    : GeomDL.RNN.unpadded_shift_failure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:29.428987+00:00
-- url     : https://prove2.me/theorems/7f1e9b87-d218-44da-9d13-09434eab8bfd
-- title:
--   §5.7, p. 92 — an unpadded RNN need not commute with a left shift
-- statement:
--   A left shift of an input sequence need not shift an RNN's hidden-state sequence by the same amount. There exist a scalar input sequence $z$, a scalar hidden-state seed $h_0$, and an update map $R:\mathbb R\times\mathbb R\to\mathbb R$ such that, with $z'(t)=z(t+1)$,
--
--   $$
--   h_{z'}(1)\ne h_z(2).
--   $$
--
--   Here each run starts from the same seed and follows $h(0)=h_0$, $h(t+1)=R(z(t+1),h(t))$. This counterexample records the boundary obstruction identified by equations (40)–(41).
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §5.7, equations (40)–(41) and following sentence, p. 92

import Mathlib
import Definitions.Def_GeomDL_RNN_Recurrence

namespace GeomDL.RNN

/-- Equations (40)–(41), p. 92: an unpadded left shift need not be equivariant. -/
theorem unpadded_shift_failure :
    ∃ (R : (Fin 1 → ℝ) → (Fin 1 → ℝ) → (Fin 1 → ℝ))
      (z : ℕ → Fin 1 → ℝ) (h0 : Fin 1 → ℝ),
      run R h0 (fun t => z (t + 1)) 1 ≠ run R h0 z 2 := by sorry

end GeomDL.RNN
