-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_K_mul
-- name    : IntMul.Kappa.R8.Bit.Oppbank.K_mul
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:00.555743+00:00
-- url     : https://prove2.me/theorems/5b542b43-f5b9-4216-bae6-e8e0536e972d
-- title:
--   The flag-basis Kronecker embedding is multiplicative
-- statement:
--   # Multiplicativity of the flag-basis Kronecker embedding
--
--   Let $S$ be a $529\times 529$ rational matrix and $S^{-1}$ a matrix of the opposite shape, and write $K(S,S^{-1};A,B)$ for the flag-basis embedding
--   $$
--   K(S,S^{-1};A,B)=S\,(A\otimes B)\,S^{-1}
--   $$
--   of a pair of $23\times 23$ rational matrices $A,B$ (the Lean name is `Pnd.K`). Assume the right inverse law $S^{-1}S=I$. Then the embedding is multiplicative in both factors:
--   $$
--   K(S,S^{-1};A,B)\,K(S,S^{-1};C,D)=K(S,S^{-1};AC,\,BD).
--   $$
--
--   This is the standard conjugation identity for Kronecker products, and is the algebraic engine of stage-one frame transport: a partial swap whose parameter is $K(\mathrm{Dm}(o,c),\mathrm{Pl}(b))$ multiplies a frame $K(\mathrm{Pc}(o),\mathrm{Pl}(b))$ into a frame $K(\mathrm{Pc}(c),\mathrm{Pl}(b))$ once the projectors compose. The statement lives on the published pack $\mathrm{Pnd}$ and does not mention a stage word.
--
--   Formalization Note. Submitted as `IntMul.Kappa.R8.Bit.Oppbank.K_mul` in the R8 FormalOK environment. Imports `Pnd` and Defs4 only; no `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: multiplicativity of Pnd.K, the R8 retarget of the R6 K_mul lemma (used by move1).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open scoped Kronecker
open Matrix
/-- Conjugated Kronecker products multiply factorwise when `Si * S = 1`. -/
theorem K_mul (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) (A B C D : M23) :
    K S Si A B * K S Si C D = K S Si (A * C) (B * D) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
