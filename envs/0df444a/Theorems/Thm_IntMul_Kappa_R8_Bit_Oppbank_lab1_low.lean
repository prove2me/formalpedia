-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_lab1_low
-- name    : IntMul.Kappa.R8.Bit.Oppbank.lab1_low
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:15:52.422078+00:00
-- url     : https://prove2.me/theorems/456c6b5a-d2ed-4be4-8ab0-ce5d74ec5415
-- title:
--   The stage-one label at the low code is the identity ($\mathrm{lab}_1(b,0)=I$)
-- statement:
--   # Stage-one labels at the low code are the identity frame
--
--   Let $S$ and $S^{-1}$ be $529\times 529$ rational matrices (the flag-basis change of the pack $\mathrm{Pnd}$), and let $N$ be a field size. The reduced stage-one label of the published pack $\mathrm{Lab}$ is
--   $$
--   \mathrm{lab}_1(S,S^{-1};N,b,c)=\mathrm{red}_N\bigl(\mathrm{pswQ}(K(S,S^{-1};\mathrm{Pc}(c),\mathrm{Pl}(b)))\bigr).
--   $$
--   The low code $c=0$ names the zero projector, $\mathrm{Pc}(0)=0$. The conjugated Kronecker product therefore vanishes in the first factor, the partial swap of the zero matrix is the identity, and reduction of the identity is again the identity:
--   $$
--   \mathrm{lab}_1(S,S^{-1};N,b,0)=I.
--   $$
--   This is the R8 retarget of the R6 identity $\mathrm{lab}_1(b,c_{\mathrm{LOW}})=I$, and is the evaluation of a stage-one label on a wire whose current code is low.
--
--   **Formalization Note.** Uses published `Lab.lab1` / `Lab.Φ₁` on `Pnd.K`, `Pnd.Pc`, `Pnd.Pl`, together with `Defs4` `pswQ` and `redM`. Does not import `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: lab1 at the low code is the identity, the R8 retarget of R6 lab1_low on Pnd/Lab (codeBound 64251).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R6.Bit
open Matrix
/-- The stage-one label at the low code is the identity frame. -/
theorem lab1_low (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (N b : ℕ) : lab1 S Si N b cLOW = 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
