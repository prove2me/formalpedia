-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_FB0_ex_Pl
-- name    : IntMul.Kappa.R8.Bit.Oppbank.FB0_ex_Pl
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:29:51.602996+00:00
-- url     : https://prove2.me/theorems/7f4c81df-eaf2-4878-b455-d2e9dde7e6ad
-- title:
--   R8 Oppbank FB0_ex on Lab0 × Pis0Pl
-- statement:
--   There exist invertible frames $S,S^{-1}$ of size $529\times(23\times 23)$ witnessing the Defs52 flag-basis property on densified labels $\mathrm{Lab0}=\{(x_T,y_T)\}$ and the Pl-only idempotent set $\mathrm{Pis0Pl}=\{\mathrm{Pl}\,T\}$. This is the Pl-restricted half of $\mathrm{FB0\_ex}$, obtained from the proved R6 lemma $\mathrm{flagBasis}$ with NetFB certificates $\mathrm{hLab0}$ and $\mathrm{hPis0Pl}$. Full $\mathrm{Pis0}$ (including densified $\mathrm{Dm}$) remains for move_facts.
-- source:
--   Jain integer-mult-kappa R6 Defs52 flagBasis; R8 NetFB Lab0/Pis0Pl retarget at codeBound=64251.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- Flag-basis inhabitance on densified Lab0 × Pis0Pl (Pl-only; full Pis0 needs move_facts). -/
theorem FB0_ex_Pl :
    ∃ (S : Matrix (Fin 529) Pr23 ℚ) (Sinv : Matrix Pr23 (Fin 529) ℚ),
      S * Sinv = 1 ∧ Sinv * S = 1 ∧
        (∀ p ∈ Lab0,
          AuxE (h := 19) (S * ((1 : M23) ⊗ₖ (1 - vecMulVec p.1 p.2)) * Sinv) ∧
            AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ (1 : M23)) * Sinv)) ∧
        (∀ p ∈ Lab0, ∀ A ∈ Pis0Pl,
          SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
            SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
        (∀ p₁ ∈ Lab0, ∀ p₂ ∈ Lab0,
          DataE (h := 19)
            (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
