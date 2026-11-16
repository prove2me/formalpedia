-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_high_of_dim
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_high_of_dim
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:10.441294+00:00
-- url     : https://prove2.me/theorems/79dc3685-ea7b-483b-a98e-277779fb426d
-- title:
--   Stage-one frames are transported from the high code at dimension less than 23
-- statement:
--   # Stage-one frame transport from the high code
--
--   Let $S$ and $S^{-1}$ be $529\times 529$ rational matrices satisfying $S^{-1}S=I$, and let $\Phi_1(b,c)$ be the stage-one frame of the published pack $\mathrm{Lab}$ as above. The high code is $1$, with $\mathrm{Pc}(1)=I$ and $\mathrm{dimCF}(1)=23$.
--
--   For every code $c<64251$ and slot $b<1771$, if either $c=1$ or $\mathrm{dimCF}(c)<23$, a move that starts at the high code transports the incoming frame to the target:
--   $$
--   \mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Dm}(1,c),\mathrm{Pl}(b))\bigr)\,\Phi_1(b,1)=\Phi_1(b,c).
--   $$
--
--   When $c=1$ the difference projector vanishes and the identity is tautological. When $\mathrm{dimCF}(c)<23$ one has $\mathrm{Dm}(1,c)=I-\mathrm{Pc}(c)$, and the partial-swap composition law together with multiplicativity of $K$ and idempotence of $\mathrm{Pl}(b)$ yield the transport. This is the $o=1$ case of the R6 identity $\mathrm{move}_1$, under the dimension hypothesis that avoids a comparison $\mathrm{dimCF}(1)\le\mathrm{dimCF}(c)$ (which would require a rank computation for a general ND code). Point codes and all densified nodes of $\mathrm{dimCF}\le 22$ are included.
--
--   Formalization Note. The Lean name is `move1_high_of_dim`. Imports `Pnd` and `Lab1` only in the problem preamble; no `QHNet` or `QHNetRec`. The general nestOK `move_1` for arbitrary ND pairs remains blocked on $\mathrm{Pc}$-rank.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: move1 from the high code on Pnd/Lab at codeBound 64251, when dimCF(c)<23 or c=1.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open Matrix
/-- A stage-one move from the high code, when the target has `dimCF < 23`
    (or is itself the high code). -/
theorem move1_high_of_dim (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hSi : Si * S = 1) {c b : ℕ} (hc : c < codeBound) (hb : b < 1771)
    (hd : c = 1 ∨ dimCF c < 23) :
    pswQ (K S Si (Dm 1 c) (Pl b)) * Φ₁ S Si b 1 = Φ₁ S Si b c := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
