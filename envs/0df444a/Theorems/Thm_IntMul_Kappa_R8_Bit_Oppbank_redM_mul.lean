-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_redM_mul
-- name    : IntMul.Kappa.R8.Bit.Oppbank.redM_mul
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:56:43.736178+00:00
-- url     : https://prove2.me/theorems/17e776ef-83c6-4d95-b6bb-9989f25c9176
-- title:
--   Reduction modulo $N$ is multiplicative on good matrices
-- statement:
--   Reduction of rational frame matrices modulo \(N\) is a ring homomorphism on the matrices whose entries have denominators coprime to \(N\).
--
--   Let \(\mathrm{red}_N\) denote the entrywise reduction of a rational \(2m\times 2m\) matrix to \(\mathbb{Z}/N\mathbb{Z}\), via the total map \(\mathbb{Q}\to\mathbb{Z}/N\mathbb{Z}\) that inverts the denominator whenever it is coprime to \(N\). If \(A,B\) are rational matrices of this size and every denominator of an entry of \(A\) or of \(B\) is coprime to \(N\), then
--   \[
--   \mathrm{red}_N(AB)=\mathrm{red}_N(A)\,\mathrm{red}_N(B).
--   \]
--   The argument is that such matrices take values in the subring \(\mathbb{Q}_{(N)}\) of rationals with denominator coprime to \(N\); reduction is a ring homomorphism on that subring, and therefore (entrywise) a homomorphism of matrix rings. Consequently the same identity holds for partial-swap frames and for the stage-one labels \(\mathrm{lab}_1=\mathrm{red}_N\circ\Phi_1\), once the factors are known to be good.
--
--   **Formalization Note.** This is the R8 packaging of the R6 identity `redMap_mul`, stated for the published `redM` of `Defs4`. The proof uses only `Defs4` / `K_Defs2` (`goodSub`, `redHom`, `redQ`) and does not import `QHNet` or `QHNetRec`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: redM is multiplicative on matrices with denominators coprime to N (R6 redMap_mul, packaged for R8 frame algebra / lab1).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
/-- Reduction modulo `N` is multiplicative on matrices whose entries have
denominators coprime to `N`. -/
theorem redM_mul {m N : ℕ} (A B : QMat2 m)
    (hA : ∀ i j, Nat.Coprime (A i j).den N)
    (hB : ∀ i j, Nat.Coprime (B i j).den N) :
    redM N (A * B) = redM N A * redM N B := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
