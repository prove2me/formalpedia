-- Prove2me | Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed
-- name    : MazurProof.N13GoodModelTwo.affineEquation_iff_fixed
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:28:11.168241+00:00
-- url     : https://prove2.me/theorems/c222862b-c39a-4d82-a654-09ae79b01aba
-- title:
--   Mazur 13 port: affineEquation_iff_fixed
-- statement:
--   In a field with four-power Frobenius, an affine point has both coordinates in the prime subfield. The non-prime-field branch is excluded by the Artin--Schreier identity, not by a finite table.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodModelTwo.lean#L195

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodModelTwo
open scoped CharTwo
open Polynomial
universe u
variable {R : Type u} [CommRing R]
variable {K : Type u} [Field K] [CharP K 2]

theorem MazurProof.N13GoodModelTwo.affineEquation_iff_fixed (hfour : ∀ z : K, z ^ 4 = z) (x y : K) : AffineEquation x y ↔ x ^ 2 = x ∧ y ^ 2 = y := by sorry
