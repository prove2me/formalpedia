-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_edgeMat_eq
-- name    : IntMul.Kappa.R8.Bit.Oppbank.edgeMat_eq
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:14:19.852731+00:00
-- url     : https://prove2.me/theorems/c37fb424-7e55-46d8-9693-70c359824b10
-- title:
--   Frame matrix of an EdgeQ edge equals redM of pswQ
-- statement:
--   # Frame matrix of a rational Bruhat edge
--
--   Let $e$ be an edge of width $m$ with rational Bruhat data realizing the partial swap of a matrix $q$ ($\mathrm{EdgeQ}\,e\,q$), and suppose the Bruhat factors $E_1(e)$ and $E_2(e)$ are good at field size $N$. Then
--
--   $$
--   \mathrm{edgeMat}_N(e)=\mathrm{redM}_N(\mathrm{pswQ}\,q).
--   $$
--
--   Uses EOKOPack `GoodM` (same denominator predicate as R6 Defs51).
--
--   **Formalization Note.** Namespace `IntMul.Kappa.R8.Bit.Oppbank`.
-- source:
--   Jain R6BitNBRed edgeMat_eq; EOKOPack GoodM

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
variable {m : ℕ}
theorem edgeMat_eq {N : ℕ} {e : Edge m} {q : Matrix (Fin m) (Fin m) ℚ}
    (he : EdgeQ e q) (h1 : GoodM N e.E₁) (h2 : GoodM N e.E₂) :
    edgeMat N e = redM N (pswQ q) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
