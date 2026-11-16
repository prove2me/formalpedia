-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_pswQ_mul
-- name    : IntMul.Kappa.R8.Bit.Oppbank.pswQ_mul
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:29:45.229006+00:00
-- url     : https://prove2.me/theorems/2d8dd0f9-6aeb-4f57-b5f7-3974d6022293
-- title:
--   Composition of partial swaps is again a partial swap
-- statement:
--   # Composition of partial swaps
--
--   Let $m$ be a natural number and let $p,p'$ be $m\times m$ rational matrices. Write $\mathrm{pswQ}(q)$ for the *partial swap* attached to a parameter $q$, namely the $2m\times 2m$ block matrix
--   $$
--   \mathrm{pswQ}(q)=\begin{pmatrix} I-q & q \\ q & I-q \end{pmatrix}
--   $$
--   acting on the doubled frame (the precise Lean representative is this block matrix, reindexed by the standard equivalence $m\oplus m\simeq 2m$).
--
--   The composition of two partial swaps is again a partial swap, with parameter equal to the Brauer–Weyl (or Temperley–Lieb) combination of the two factors:
--   $$
--   \mathrm{pswQ}(p)\,\mathrm{pswQ}(p')=\mathrm{pswQ}\bigl(p+p'-2\,p p'\bigr).
--   $$
--
--   This identity is the rational-matrix form of edge composition in the flag-basis network: it is what lets a stage frame $\Phi_1(b,c)=\mathrm{pswQ}\bigl(K(\mathrm{Pc}(c),\mathrm{Pl}(b))\bigr)$ be transported along a move whose edge projector is a difference $\mathrm{Dm}(o,c)$. The statement is over $\mathbb{Q}$ and does not depend on the densified code bound or on the packs $\mathrm{Pnd}$ and $\mathrm{Lab}$.
--
--   Formalization Note. The constant is `pswQ` from the published Defs4 pack, submitted in the R8 FormalOK environment as `IntMul.Kappa.R8.Bit.Oppbank.pswQ_mul`. No `QHNet` or `QHNetRec` import.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: pswQ composition identity, the R8 retarget of the R6 pswQ_mul lemma on Defs4 (used by move1).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit.NB
open Matrix
/-- Composition of partial swaps is the partial swap of the Brauer–Weyl combination. -/
theorem pswQ_mul {m : ℕ} (p p' : Matrix (Fin m) (Fin m) ℚ) :
    pswQ p * pswQ p' = pswQ (p + p' - 2 * (p * p')) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
