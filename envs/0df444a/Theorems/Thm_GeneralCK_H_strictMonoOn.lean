-- Prove2me | Theorems.Thm_GeneralCK_H_strictMonoOn
-- name    : GeneralCK.H_strictMonoOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:53:17.806006+00:00
-- url     : https://prove2.me/theorems/31201542-a636-429b-8568-e4bcc127a867
-- title:
--   Strict increase of binary entropy below one half
-- statement:
--   Let $H(p)=[-p\log p-(1-p)\log(1-p)]/\log2$ be binary entropy in bits, with its continuous endpoint values. For real $a,b$ satisfying $0\le a<b\le\tfrac12$, $$H(a)<H(b).$$ This strict monotonicity makes the entropy inverse on the lower half of the unit interval well defined and is reused throughout the analytic proof.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileBasics.lean#L5-L9

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open GeneralCK

theorem GeneralCK.H_strictMonoOn : StrictMonoOn H (Set.Icc 0 (1 / 2)) := by sorry
