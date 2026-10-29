-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_genF_locals_of_W
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_genF_locals_of_W
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:48:59.85935+00:00
-- url     : https://prove2.me/theorems/3b01b3bc-cc37-4a0d-82aa-08d002a558ff
-- title:
--   genF chunk locals come from the input word wires
-- statement:
--   Every local endpoint stored in a chunk of \(\mathrm{genF}(f,W)\) already appears among the wires of some instruction of \(W\).
--
--   Writing \(L=\mathrm{genF}(f,W).2\) for the produced chunk list, if \(\ell\) is a move first-component or an XOR endpoint inside some \(\mathrm{ch}\in L\), then
--   $$
--   \exists\, i\in W,\qquad \ell\in i.\mathsf{touch}\ \text{or}\ \ell\ \text{is an XOR endpoint of}\ i.
--   $$
--
--   This is the structural half of the \(\mathrm{cs1}\) local-bound densify (independent of LocSlots numerals).
--
--   Formalization Note. Follows by induction on \(\mathrm{foldl\ genStepF}\): each fresh chunk's moves are produced by \(\mathrm{foldl\ mvF}\) on that instruction's touch list, and its XOR list is copied verbatim.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: genF local-preservation

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
theorem net0O2_genF_locals_of_W (f : ℕ → ℕ) (W : List LInstr) (ℓ : ℕ)
    (hℓ : ∃ ch ∈ (genF f W).2,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ∃ i ∈ W, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
