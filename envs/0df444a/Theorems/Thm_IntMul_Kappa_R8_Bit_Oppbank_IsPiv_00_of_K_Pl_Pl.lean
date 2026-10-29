-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_IsPiv_00_of_K_Pl_Pl
-- name    : IntMul.Kappa.R8.Bit.Oppbank.IsPiv_00_of_K_Pl_Pl
-- status  : Disproved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:53:49.598845+00:00
-- url     : https://prove2.me/theorems/a53dbafa-05e3-4dd7-a1a0-e27a8370d805
-- title:
--   K(S,Si,Pl a, Pl s) has pivot at (0,0) under FB0
-- statement:
--   Let \(S,S_i\) be reciprocal frames (\(SS_i=S_iS=I\)) and let \(\mathrm{Pl}\,a,\mathrm{Pl}\,s\) be the densified projectors for banks \(a,s<1771\). Then the corner matrix \(K(S,S_i,\mathrm{Pl}\,a,\mathrm{Pl}\,s)\) has a rank-pivot at position \((0,0)\):
--
--   $$
--   \mathrm{IsPiv}\bigl(K(S,S_i,\mathrm{Pl}\,a,\mathrm{Pl}\,s),0,0\bigr).
--   $$
--
--   This replaces the unsound general claim that every rank-one matrix is pivoted at \((0,0)\).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit.NB (IsPiv)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem IsPiv_00_of_K_Pl_Pl (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a s : ℕ} (ha : a < 1771) (hs : s < 1771) :
    IsPiv (K S Si (Pl a) (Pl s)) 0 0 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
