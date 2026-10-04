-- Prove2me | Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
-- name    : LodhaMoore.bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T06:54:43.823036+00:00
-- url     : https://prove2.me/theorems/38c8cb33-a7a4-405e-9a87-b5de11f362ed
-- title:
--   §3 — every x_s and y_s is a bijection, and the relations (1)–(5) hold
-- statement:
--   Every $x_s$ and every $y_s$ is a bijection of the infinite binary sequences, so the generators `xs s`, `ys s` are these functions (not the identity the definitions fall back to otherwise). Every relation of $R$ holds for them: for every finite $s$, $t$, (1) $x_s^2 = x_{s0}x_sx_{s1}$; (2) if $t.x_s$ is defined, $x_tx_s = x_sx_{t.x_s}$; (3) if $t.x_s$ is defined, $y_tx_s = x_sy_{t.x_s}$; (4) if $s$ and $t$ are incompatible, $y_sy_t = y_ty_s$; (5) $y_s = x_sy_{s0}y_{s10}^{-1}y_{s11}$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 6, §3, relations (1)–(5)

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R :
    (∀ s, Function.Bijective (xSeq s) ∧ Function.Bijective (ySeq s)) ∧
      ∀ r ∈ R, FreeGroup.lift Gen.val r = 1 := by
  sorry

end LodhaMoore
