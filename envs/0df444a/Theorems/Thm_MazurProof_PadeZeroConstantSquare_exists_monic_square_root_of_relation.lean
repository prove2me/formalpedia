-- Prove2me | Theorems.Thm_MazurProof_PadeZeroConstantSquare_exists_monic_square_root_of_relation
-- name    : MazurProof.PadeZeroConstantSquare.exists_monic_square_root_of_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:25:20.775523+00:00
-- url     : https://prove2.me/theorems/1374fc5e-9d2a-4772-8ae7-03c04e45052e
-- title:
--   Mazur 13 port: exists_monic_square_root_of_relation
-- statement:
--   A unit-times-square identity with a monic quadratic-or-smaller factor forces that factor to be a monic square.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/PadeZeroConstantSquare.lean#L57

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
variable {K : Type*} [Field K]

theorem MazurProof.PadeZeroConstantSquare.exists_monic_square_root_of_relation {q a l u : K[X]} (hq : IsUnit q) (hl : l ≠ 0) (huMonic : u.Monic) (huDeg : u.natDegree ≤ 2) (hRelation : q * l ^ 2 = a ^ 2 * u) : ∃ b : K[X], b.Monic ∧ b.natDegree ≤ 1 ∧ u = b ^ 2 := by sorry
