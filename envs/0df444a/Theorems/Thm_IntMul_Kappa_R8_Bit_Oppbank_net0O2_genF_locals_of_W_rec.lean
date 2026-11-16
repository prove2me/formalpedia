-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_genF_locals_of_W_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_genF_locals_of_W_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:01:51.898614+00:00
-- url     : https://prove2.me/theorems/3c638401-fa37-487f-8281-eea99baa9e21
-- title:
--   Locals stored by genF already appear on the input word W (QHNetRec)
-- statement:
--   Every local endpoint stored in the chunk list of the densified generator \(\mathrm{genF}(f,W)\) already appears on some instruction of the input word \(W\), on the total-decoder network `QHNetRec`.
--
--   Let \(f:\mathbb{N}\to\mathbb{N}\) be a seed code map and let \(W\) be a list of local instructions. Write \(\mathrm{genF}(f,W)_2\) for the generated chunk list. If a local index \(\ell\) occurs as a move source or as an XOR endpoint in some chunk of that list, then the same index already occurs on some instruction \(i\in W\):
--
--   $$
--   \exists\, i\in W.\qquad \ell\in i_{2,1}\quad\text{or}\quad \exists\, p\in i_{2,2}.\ (p_1=\ell\lor p_2=\ell).
--   $$
--
--   This is the local-preservation lemma for \(\mathrm{genF}\). Combined with the \(W_{1F}\) wire bound it is the data-bound leaf of the \(\mathrm{cs1}\) densify in the QHNetRec environment.
--
--   **Formalization Note.** The statement is identical to `net0O2_genF_locals_of_W`, with preamble importing `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec` rather than `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`. It does not import the parent QHNet module and does not close or replace `3b01b3bc-cc37-4a0d-82aa-08d002a558ff`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: genF local-preservation, restated on the total-decoder fork IntMul_Kappa_R8_Data_BitOppbankQHNetRec (d127abea). Does not close or replace 3b01b3bc-cc37-4a0d-82aa-08d002a558ff.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
theorem net0O2_genF_locals_of_W_rec (f : ℕ → ℕ) (W : List LInstr) (ℓ : ℕ)
    (hℓ : ∃ ch ∈ (genF f W).2,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ∃ i ∈ W, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
