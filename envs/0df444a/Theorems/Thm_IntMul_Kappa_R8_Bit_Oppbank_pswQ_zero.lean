-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pswQ_zero
-- name    : IntMul.Kappa.R8.Bit.Oppbank.pswQ_zero
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:01:30.284204+00:00
-- url     : https://prove2.me/theorems/47fb10aa-2b27-4f85-907e-1cef265b0e72
-- title:
--   The partial swap of zero is the identity frame
-- statement:
--   The rational partial-swap frame of the zero matrix is the identity.
--
--   For a square rational matrix \(q\) of size \(m\), the partial swap is the \(2m\times 2m\) block matrix
--   \[
--   \mathrm{pswQ}(q)=\begin{pmatrix} I-q & q \\ q & I-q \end{pmatrix},
--   \]
--   reindexed by the standard sum-equivalence \(\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m\simeq\mathrm{Fin}(m+m)\). Substituting \(q=0\) yields the identity on each diagonal block and zero off the diagonal, hence
--   \[
--   \mathrm{pswQ}(0)=I.
--   \]
--   Together with \(\mathrm{Pc}(0)=0\) and multiplicativity of \(\mathrm{red}_N\), this is the evaluation of a stage-one label at a low-code wire: the corresponding frame reduces to the identity.
--
--   **Formalization Note.** Packaged for the R8 frame-algebra chain (`lab1_low` / \(\Phi_1\)). The proof uses only the published `pswQ` of `Defs4` and does not import `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: pswQ 0 = 1, used for lab1 at the low code (with Pc_low and redM).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit.NB
open Matrix
/-- The partial swap of the zero matrix is the identity frame. -/
theorem pswQ_zero {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
