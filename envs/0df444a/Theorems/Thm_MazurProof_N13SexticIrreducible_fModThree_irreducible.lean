-- Prove2me | Theorems.Thm_MazurProof_N13SexticIrreducible_fModThree_irreducible
-- name    : MazurProof.N13SexticIrreducible.fModThree_irreducible
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:32:13.823585+00:00
-- url     : https://prove2.me/theorems/2b6c6405-7ea6-4396-87d7-add393fb2067
-- title:
--   Mazur 13 port: fModThree_irreducible
-- statement:
--   The reduction of the N13 sextic modulo three is irreducible.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SexticIrreducible.lean#L133

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SexticIrreducible
open Polynomial

theorem MazurProof.N13SexticIrreducible.fModThree_irreducible : Irreducible fModThree := by sorry
