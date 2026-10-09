-- Prove2me | Theorems.Thm_MazurProof_RamifiedDlog_fst_ne_zero
-- name    : MazurProof.RamifiedDlog.fst_ne_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:27:00.89443+00:00
-- url     : https://prove2.me/theorems/8faf286f-68d7-42e5-85fd-ebafb7ce6f5c
-- title:
--   Mazur 13 port: fst_ne_zero
-- statement:
--   The residue of a dual-number unit is nonzero.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/RamifiedDlog.lean#L36

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TrivSqZeroExt
variable {k : Type*} [Field k]

theorem MazurProof.RamifiedDlog.fst_ne_zero (z : (DualNumber k)ˣ) : fst (z : DualNumber k) ≠ 0 := by sorry
