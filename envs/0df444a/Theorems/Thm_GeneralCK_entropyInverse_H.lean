-- Prove2me | Theorems.Thm_GeneralCK_entropyInverse_H
-- name    : GeneralCK.entropyInverse_H
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:56:40.931956+00:00
-- url     : https://prove2.me/theorems/be7c4c2c-b906-44f4-abba-25161e417bb5
-- title:
--   The lower entropy inverse recovers the smaller complementary probability
-- statement:
--   Define $H$ as binary entropy in bits and $q(h)=\inf\{v\in[0,\tfrac12]:h\le H(v)\}$. For every real $m\in[0,1]$, $$q(H(m))=\min\{m,1-m\}.$$ The formula combines inversion on the lower half interval with entropy's symmetry under complementation.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileBasics.lean#L27-L32

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman

open GeneralCK

theorem GeneralCK.entropyInverse_H {m : ℝ} (hm : 0 ≤ m) (hm' : m ≤ 1) :
    entropyInverse (H m) = min m (1 - m) := by sorry
