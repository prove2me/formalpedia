-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_move1_low
-- name    : IntMul.Kappa.R8.Bit.Oppbank.move1_low
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:30:00.796202+00:00
-- url     : https://prove2.me/theorems/44b870a6-d305-4cb7-bc93-9c76cbbeaa02
-- title:
--   Stage-one frames are transported from the low code
-- statement:
--   # Stage-one frame transport from the low code
--
--   Let $S$ and $S^{-1}$ be $529\times 529$ rational matrices, and let $\Phi_1(b,c)=\mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Pc}(c),\mathrm{Pl}(b))\bigr)$ be the stage-one frame of the published pack $\mathrm{Lab}$ at slot $b$ and code $c$. Write $\mathrm{Dm}(o,c)$ for the difference of the two named projectors, oriented by the comparison of $\mathrm{dimCF}$. The densified code bound is $64251$.
--
--   For every code $c<64251$ and every slot $b<1771$, a move that starts at the *low* code $0$ transports the incoming frame to the target:
--   $$
--   \mathrm{pswQ}\bigl(K(S,S^{-1};\mathrm{Dm}(0,c),\mathrm{Pl}(b))\bigr)\,\Phi_1(b,0)=\Phi_1(b,c).
--   $$
--
--   The identity needs no nesting hypothesis: the low projector is zero, $\mathrm{dimCF}(0)=0$ is minimal so $\mathrm{Dm}(0,c)=\mathrm{Pc}(c)$, and the incoming frame $\Phi_1(b,0)$ is the identity. This is the first (and algebraically simplest) case of the R6 move identity $\mathrm{move}_1$, retargeted to the densified R8 packs $\mathrm{Pnd}$ and $\mathrm{Lab}$. It covers in particular every start from the zero code, including the `copyo` overwrites $0\mapsto\mathrm{cND}(t+1)$. The general nestOK case for arbitrary ND codes remains a separate lemma (it still uses $\mathrm{Pc}$-rank).
--
--   Formalization Note. The Lean name is `move1_low` (ASCII). Imports `Pnd` and `Lab1` only; no `QHNet` or `QHNetRec`. The bound hypotheses $c<64251$ and $b<1771$ are recorded to match the intended domain of $\mathrm{move}_1$, even though the algebraic cancellation does not use them.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: move1 from the low code on Pnd/Lab at codeBound 64251, the o=0 case of the R6 move1 identity.

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
/-- A stage-one move from the low code: `pswQ(K(Dm 0 c, Pl b)) * Φ₁ b 0 = Φ₁ b c`. -/
theorem move1_low (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    {c b : ℕ} (hc : c < codeBound) (hb : b < 1771) :
    pswQ (K S Si (Dm 0 c) (Pl b)) * Φ₁ S Si b 0 = Φ₁ S Si b c := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
