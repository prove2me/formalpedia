-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_append
-- name    : IntMul.Kappa.R8.Bit.Oppbank.LabGates_append
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:27:53.187083+00:00
-- url     : https://prove2.me/theorems/b33ec8e6-fa66-4aee-99d0-8ae5ac5e0777
-- title:
--   LabGates is compatible with program concatenation
-- statement:
--   Label-gate consistency concatenates. For instruction lists \(l_1,l_2\) and an initial frame labeling \(L\),
--
--   $$
--   \mathrm{LabGates}\,N\,(l_1{+}{+}l_2)\,L
--   \quad\Longleftrightarrow\quad
--   \mathrm{LabGates}\,N\,l_1\,L
--   \;\wedge\;
--   \mathrm{LabGates}\,N\,l_2\,(l_1.\mathrm{foldl}\,(\mathrm{labStepH}\,N)\,L).
--   $$
--
--   This is the structural densification step for assembling `LabGates` of `net0O.prog` from its stage blocks.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (LabGates labStepH FMat)
theorem LabGates_append {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (l₁ l₂ : List (IntMul.Kappa.R6.Bit.Instr Wr R m))
    (L : Wr → FMat m N) :
    LabGates N (l₁ ++ l₂) L ↔
      LabGates N l₁ L ∧ LabGates N l₂ (l₁.foldl (labStepH N) L) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
