-- Prove2me | Theorems.Thm_J6Seg_Side_axJ_ev
-- name    : J6Seg.Side.axJ_ev
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:46:19.172806+00:00
-- url     : https://prove2.me/theorems/2a79c35d-b830-4695-86fc-444e6f4d3917
-- title:
--   AxJ eventually on every round-six axis
-- statement:
--   For every admissible round-six parameter record $P$ there exists a threshold $n_1$ such that for all $n\ge n_1$ and every admissible source list, every axis carries an `AxJ` witness (side bounds, segment regularity, and window hypotheses).
--
--   This is the numeric input to `jBudget6_all`.
-- source:
--   xuanji round-six κ; Solutions.J6SegJCost3

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.Side
open IntMul.Kappa.R6

namespace J6Seg.Side

theorem axJ_ev (P : IntMul.Kappa.R6.Prm) (hP : P.Ok) :
    ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ,
      IntMul.Kappa.R6.SrcOK6 P n src → ∀ D : ℕ, IntMul.Kappa.R6.dP6 P n = D + 1 →
      ∀ k ≤ D, AxJ P n src D k := by
  sorry

end J6Seg.Side
