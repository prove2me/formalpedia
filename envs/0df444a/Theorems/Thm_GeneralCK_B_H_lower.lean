-- Prove2me | Theorems.Thm_GeneralCK_B_H_lower
-- name    : GeneralCK.B_H_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:57:53.008812+00:00
-- url     : https://prove2.me/theorems/725a8aec-1170-4983-9b29-67b153260885
-- title:
--   The Bellman profile vanishes on the lower entropy cap
-- statement:
--   Let $H$ be binary entropy in bits and $B(m,h)=\max\{\phi(m,h),\psi(m,h)\}$ be the combined Bellman profile from the mission's analytic interface. For every real $m$ with $0<m\le\tfrac12$, $$B(m,H(m))=0.$$ This supplies the lower half of the boundary condition used by the Bellman reduction.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileBasics.lean#L64-L75

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman

open GeneralCK

theorem GeneralCK.B_H_lower {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1 / 2) : B m (H m) = 0 := by sorry
