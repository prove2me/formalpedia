-- Prove2me | Theorems.Thm_MazurProof_N13ReciprocalInfinityContraction_goodYbar_relation
-- name    : MazurProof.N13ReciprocalInfinityContraction.goodYbar_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:45:41.95898+00:00
-- url     : https://prove2.me/theorems/ab33acbd-4b98-44dc-b787-d1d4453ea4d7
-- title:
--   Mazur 13 port: goodYbar_relation
-- statement:
--   Supporting lemma `goodYbar_relation` (namespace `MazurProof.N13ReciprocalInfinityContraction`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13ReciprocalInfinityContraction.lean#L209

import Mathlib
import Definitions.Def_MazurN13_L1

open MazurProof MazurProof.N13ReciprocalInfinityContraction
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13ReciprocalInfinityContraction.goodYbar_relation (D : SexticMumford.Mumford Model) : goodYbar D ^ 2 + (xbar D ^ 3 + xbar D + 1) * goodYbar D = xbar D ^ 5 + xbar D ^ 4 := by sorry
