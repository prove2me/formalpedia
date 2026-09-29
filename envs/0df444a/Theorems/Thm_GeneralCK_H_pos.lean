-- Prove2me | Theorems.Thm_GeneralCK_H_pos
-- name    : GeneralCK.H_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:53:20.374972+00:00
-- url     : https://prove2.me/theorems/053ca6a6-5649-42d0-837e-d32326d1b66d
-- title:
--   Positivity of binary entropy in the open unit interval
-- statement:
--   For every real $p$ with $0<p<1$, binary entropy in bits satisfies $$H(p)>0.$$ Here $H(p)=[-p\log p-(1-p)\log(1-p)]/\log2$. This positivity supplies the signs needed by the profile and correction arguments.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileBasics.lean#L11-L12

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open GeneralCK

theorem GeneralCK.H_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) : 0 < H p := by sorry
