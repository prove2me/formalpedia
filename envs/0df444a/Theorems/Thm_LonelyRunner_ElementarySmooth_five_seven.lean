-- Prove2me | Theorems.Thm_LonelyRunner_ElementarySmooth_five_seven
-- name    : LonelyRunner.ElementarySmooth.five_seven
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-06T01:14:22.937554+00:00
-- url     : https://prove2.me/theorems/1bb32047-cf10-4ee5-b28f-ce1cc4b6e356
-- title:
--   Prime factors forced by a Goddyn–Wong tripling window
-- statement:
--   Let $n$ and $s$ be natural numbers with $s<n$, and put $c=n-s$. Assume that no integer $b$ with $c\le b<3c$ is coprime to $s$. Then
--
--   $$5\mid s \quad\text{or}\quad 7\mid s \quad\text{or}\quad c=8.$$
--
--   This elementary restriction supplies smooth-number intervals in a two-replacement Lonely Runner argument. This is AI-assisted research; novelty has not been independently reviewed.
-- source:
--   Wade Hunter, AI-assisted Lonely Runner research, local commit 78c23c6, lean/LonelyRunner/ElementarySmooth.lean, theorem five_seven; repository https://github.com/huntrontrakkr/lonely-runner

import Definitions.Def_LRC_GW
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
open LonelyRunner.SeparatedReplacements

theorem LonelyRunner.ElementarySmooth.five_seven {n s : ℕ} (hsn : s < n) (hgw : GW n s 3) :
    5 ∣ s ∨ 7 ∣ s ∨ n-s=8 := by sorry
