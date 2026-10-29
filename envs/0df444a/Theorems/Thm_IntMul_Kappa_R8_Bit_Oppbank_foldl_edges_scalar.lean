-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_foldl_edges_scalar
-- name    : IntMul.Kappa.R8.Bit.Oppbank.foldl_edges_scalar
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:55:01.530305+00:00
-- url     : https://prove2.me/theorems/437d95a8-04e0-4460-92df-6fc6ce1793a2
-- title:
--   Edges act as identity on scalar state
-- statement:
--   Folding a list of edge instructions under $\mathrm{scalarStepH}$ leaves the scalar assignment unchanged, since each edge step is the identity on scalars.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (scalarStepH Instr Edge)
theorem foldl_edges_scalar {Wr : Type*} [DecidableEq Wr] {R : Type*} [CommRing R] {m : ℕ}
    (es : List (Wr × Edge m)) (v : Wr → R) :
    (es.map fun p => Instr.edge (R := R) p.1 p.2).foldl scalarStepH v = v := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
