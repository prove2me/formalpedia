-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_of_Le_dim
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_of_Le_dim
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:40:51.076536+00:00
-- url     : https://prove2.me/theorems/1883b0d2-4966-4e21-9dac-692021102f35
-- title:
--   Stage-one frame transport under a matching Le of projectors
-- statement:
--   # Stage-one frame transport under a matching nesting of projectors
--
--   Let $S$ and $S^{-1}$ be $529\times 529$ rational matrices satisfying $S^{-1}S=I$. Write $\mathrm{Pc}(c)$ for the densified code projector, $\mathrm{Pl}(b)$ for the point projector at slot $b$, and $\mathrm{Dm}(o,c)$ for their difference, oriented by the comparison of recorded dimensions $\mathrm{dimCF}$: $\mathrm{Dm}(o,c)=\mathrm{Pc}(c)-\mathrm{Pc}(o)$ when $\mathrm{dimCF}(o)\le\mathrm{dimCF}(c)$, and $\mathrm{Pc}(o)-\mathrm{Pc}(c)$ otherwise. Let $\Phi_1(b,c)=\mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Pc}(c),\mathrm{Pl}(b))\bigr)$ be the stage-one frame of the published pack $\mathrm{Lab}$. Write $\mathrm{Le}(A,B)$ for the nesting relation $BA=A=AB$ of idempotents.
--
--   For every pair of codes $o,c<64251$ and every slot $b<1771$, if the orientation of $\mathrm{Dm}(o,c)$ is compatible with a nesting of the two projectors — that is, either
--   $$
--   \mathrm{dimCF}(o)\le\mathrm{dimCF}(c)\quad\text{and}\quad\mathrm{Le}\bigl(\mathrm{Pc}(o),\mathrm{Pc}(c)\bigr),
--   $$
--   or the opposite dimension comparison together with $\mathrm{Le}\bigl(\mathrm{Pc}(c),\mathrm{Pc}(o)\bigr)$ — then a move from $o$ to $c$ transports the incoming frame:
--   $$
--   \mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Dm}(o,c),\mathrm{Pl}(b))\bigr)\,\Phi_1(b,o)=\Phi_1(b,c).
--   $$
--
--   The identity is purely algebraic: it uses the composition law for partial swaps, the multiplicativity of $K$ under $S^{-1}S=I$, and the idempotence of $\mathrm{Pc}(o)$ and $\mathrm{Pl}(b)$. It does not use the rank of $\mathrm{Pc}$, nor the soundness of the boolean predicate $\mathrm{nestOK}$. In this sense it is the general $R8$ form of the $R6$ move identity $\mathrm{move}_1$, under the hypothesis that $\mathrm{Le}$ is already aligned with $\mathrm{dimCF}$. The two previously established special cases (a move from the zero code, and a move from the high code when $\mathrm{dimCF}(c)<23$) are instances. Closing the remaining gap from $\mathrm{nestOK}$ to a matching $\mathrm{Le}$ is a separate soundness lemma; the mismatched-dimension equal-projector case continues to use a rank comparison.
--
--   Formalization Note. The Lean name is `move1_of_Le_dim`. Imports `Pnd`, `Lab1`, and `MoveFacts2` (for $\mathrm{Le}$) in the problem preamble; the solution additionally uses `MoveFacts3` for $\mathrm{Pc}$-idempotence and `NetFB`/`ProjB` for $\mathrm{Pl}$-idempotence. No `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: general algebraic move1 on Pnd+Lab1, under Le aligned with dimCF (no Pc-rank, no nestOK soundness).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open Matrix
/-- Stage-one move when `Dm` is oriented with a matching `Le` hypothesis
    (no `Pc`-rank and no `nestOK` soundness). -/
theorem move1_of_Le_dim (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {o c b : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hb : b < 1771)
    (h : (dimCF o ≤ dimCF c ∧ Le (Pc o) (Pc c)) ∨
         (¬ dimCF o ≤ dimCF c ∧ Le (Pc c) (Pc o))) :
    pswQ (K S Si (Dm o c) (Pl b)) * Φ₁ S Si b o = Φ₁ S Si b c := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
