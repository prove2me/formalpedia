-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_goodK
-- name    : IntMul.Kappa.R8.Bit.Oppbank.goodK
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:15:43.768208+00:00
-- url     : https://prove2.me/theorems/55b40602-f2c1-456e-bbf9-9e11cfa6c31a
-- title:
--   The conjugated Kronecker product $K$ preserves good denominators
-- statement:
--   # Good denominators are preserved by flag-basis conjugation
--
--   Write $K(S,S^{-1};A,B)=S(A\otimes B)S^{-1}$ for the conjugated Kronecker product of the published pack $\mathrm{Pnd}$, and say that a rational matrix is good at $N$ when every entry has denominator coprime to $N$ (the predicate $\mathrm{GoodM}$ of the pack $\mathrm{Lab}$). If $S$, $S^{-1}$, $A$ and $B$ are all good at $N$, then so is the conjugate:
--   $$
--   \mathrm{GoodM}_N(S),\ \mathrm{GoodM}_N(S^{-1}),\ \mathrm{GoodM}_N(A),\ \mathrm{GoodM}_N(B)
--   \implies
--   \mathrm{GoodM}_N\bigl(K(S,S^{-1};A,B)\bigr).
--   $$
--   The claim is immediate from the ring of coprime-denominator rationals: it is closed under multiplication and addition, hence under Kronecker products and matrix products. This is the R8 retarget of the R6 lemma $\mathrm{good}K$, and is the denominator hypothesis needed to reduce stage frames $\Phi_1$ and move matrices modulo $N$.
--
--   **Formalization Note.** `GoodM` and $K$ are from the published packs `Lab` and `Pnd`. The argument does not import `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: goodK, the R8 retarget of R6 goodK on Pnd.K and Lab.GoodM (codeBound 64251).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open Matrix
/-- The conjugated Kronecker product preserves good denominators. -/
theorem goodK {S : Matrix (Fin 529) Pr23 ℚ} {Si : Matrix Pr23 (Fin 529) ℚ} {N : ℕ}
    (hS : GoodM N S) (hSi : GoodM N Si) {A B : M23}
    (hA : GoodM N A) (hB : GoodM N B) : GoodM N (K S Si A B) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
