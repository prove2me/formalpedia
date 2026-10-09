-- Prove2me | Theorems.Thm_MazurProof_N13GaussianDifferentSupport_normalizedKummerInteger_eq_unit_mul_sq
-- name    : MazurProof.N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T07:40:00.473982+00:00
-- url     : https://prove2.me/theorems/ac0c5099-688d-4e95-a64a-03d1313cbfaf
-- title:
--   Mazur 13 port: normalizedKummerInteger_eq_unit_mul_sq
-- statement:
--   The normalized Kummer integer is already a unit times a square in the maximal order. The proof first leaves only the two primes supporting the different, and then separates their two parity bits by the absolute ideal norm at `2` and `13`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianDifferentSupport.lean#L949

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianDifferentSupport
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open IsDedekindDomain
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.numberFieldL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fractionRingOL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.intAlgebraO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.dedekindRelativeO
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeGIL
attribute [local instance] MazurProof.N13GaussianDifferentSupport.torsionFreeRelativeO

theorem MazurProof.N13GaussianDifferentSupport.normalizedKummerInteger_eq_unit_mul_sq (D : N13LowDegreeKummerHom.LowRep) : ∃ ε : Oˣ, ∃ y : O, normalizedKummerInteger D = (ε : O) * y ^ 2 := by sorry
