-- Prove2me | Theorems.Thm_LatticePrepro_ObliviousPCP_card_coord
-- name    : LatticePrepro.ObliviousPCP.card_coord
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-16T22:10:33.995887+00:00
-- url     : https://prove2.me/theorems/7217774f-0425-4c1c-a839-7ba9ae7edb3e
-- title:
--   Theorem 6.4 (size) — the accepting-view code has block length $(|\Sigma|+\Gamma)\cdot Y+1$
-- statement:
--   For the accepting-view code of Construction 6.2, built from a query-oblivious PCP with alphabet $\Sigma$, $\mathsf R$ random bits and $\mathsf q$ queries, an encoding map into $F^{B}$ and an integer $\Gamma\ge0$, the block length is
--   $$M=M_0+H=(|\Sigma|+\Gamma)\cdot Y+1,\qquad Y=B\cdot2^{\mathsf R}\cdot\mathsf q .$$
--   Here $M_0=|\Sigma|\cdot Y$ is the number of rows of $G_1$ and $H=\Gamma\cdot Y+1$ is the number of padding coordinates.
--
--   This is the block length stated in Theorem 6.4.
--
--   **Formalization Note.** The statement computes the cardinality of the coordinate type `P.Coord B ⊕ Fin (g * P.radius B + 1)` of the code, where `P.Coord B` is $\{0,1\}^{\mathsf R}\times[\mathsf q]\times\Sigma\times[B]$ and `P.radius B` is $Y$. It involves neither the field nor the encoding map. The Lean names `g`, `ρ`, `q` stand for $\Gamma$, $\mathsf R$, $\mathsf q$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Theorem 6.4 (\label{thm:pcp-reduction}), size, with step 4 of Construction 6.2 (\label{con:pcp-reduction}); Lean: LatticePrepro/PCP/Code.lean, LatticePrepro.ObliviousPCP.card_coord

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]
variable {F} {B : ℕ}

theorem LatticePrepro.ObliviousPCP.card_coord (B g : ℕ) :
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 := by sorry
