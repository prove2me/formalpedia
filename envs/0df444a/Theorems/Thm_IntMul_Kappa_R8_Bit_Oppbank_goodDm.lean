-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_goodDm
-- name    : IntMul.Kappa.R8.Bit.Oppbank.goodDm
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:15:49.56427+00:00
-- url     : https://prove2.me/theorems/61049b13-b841-45bd-804c-1c4a28c7745d
-- title:
--   The move matrix $D_m$ of two good projectors is good
-- statement:
--   # The move idempotent between good code projectors is good
--
--   For codes $o$ and $c$, the move matrix of the published pack $\mathrm{Pnd}$ is the difference of projectors in the direction of increasing dimension,
--   $$
--   D_m(o,c)=\begin{cases}
--   \mathrm{Pc}(c)-\mathrm{Pc}(o) & \text{if }\dim(o)\le\dim(c),\\
--   \mathrm{Pc}(o)-\mathrm{Pc}(c) & \text{otherwise.}
--   \end{cases}
--   $$
--   If both projectors are good at $N$ (every denominator coprime to $N$), then so is the difference:
--   $$
--   \mathrm{GoodM}_N(\mathrm{Pc}(o)),\ \mathrm{GoodM}_N(\mathrm{Pc}(c))
--   \implies
--   \mathrm{GoodM}_N\bigl(D_m(o,c)\bigr).
--   $$
--   This is the R8 retarget of the R6 lemma $\mathrm{good}D_m$, used with $\mathrm{good}K$ to reduce a stage-one move $\mathrm{pswQ}(K(D_m(o,c),\mathrm{Pl}(b)))$ modulo $N$.
--
--   **Formalization Note.** `Dm` and `Pc` are from published `Pnd`; `GoodM` is from published `Lab`. Does not import `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: goodDm, the R8 retarget of R6 goodDm on Pnd.Dm and Lab.GoodM (codeBound 64251).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
/-- The move idempotent between two good code projectors is good. -/
theorem goodDm {N o c : ℕ} (ho : GoodM N (Pc o)) (hc : GoodM N (Pc c)) :
    GoodM N (Dm o c) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
