-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_low
-- name    : IntMul.Kappa.R8.Bit.Oppbank.Pc_low
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:56:54.588977+00:00
-- url     : https://prove2.me/theorems/14bcc495-7888-4661-a0e8-a4eff0a9a2bc
-- title:
--   The low-code projector is zero ($\mathrm{Pc}(0)=0$)
-- statement:
--   On the densified R8 opp-bank code projectors, the projector named by the low code is the zero matrix.
--
--   The code-to-projector map \(\mathrm{Pc}\) of the published pack \(\mathrm{Pnd}\) is defined by cases on the code \(c\):
--   \[
--   \mathrm{Pc}(c)=
--   \begin{cases}
--   0 & \text{if }c=0,\\
--   I & \text{if }c=1,\\
--   I-\mathrm{Pl}(c-2) & \text{if }2\le c<1773,\\
--   \mathrm{Pnd}(\mathrm{densSupG}(c-1773)) & \text{if }c\ge 1773.
--   \end{cases}
--   \]
--   In particular the low code \(c=0\) names the zero projector on \(\mathbb{Q}^{23}\):
--   \[
--   \mathrm{Pc}(0)=0.
--   \]
--   This is the R8 retarget of the corresponding R6 identity, and is used to evaluate stage-one frames at a wire whose current code is low (for instance \(\mathrm{lab}_1(b,0)\) reduces to the identity frame). The bound on codes is the densified \(\mathrm{codeBound}=64251\), not the R6 bound \(38286\).
--
--   **Formalization Note.** The statement uses the published R8 `Pnd.Pc` (honest ND branch, `codeBound=64251`). It does not import `QHNet` or `QHNetRec`, and does not use the stale `Gen.ValidOn` bound \(38286\).
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: Pc 0 = 0 on published Pnd (codeBound 64251), the R8 retarget of the R6 low-code projector identity.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
/-- The projector named by the low code is the zero matrix. -/
theorem Pc_low : Pc 0 = 0 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
