-- Prove2me | Theorems.Thm_GeneralCK_Information_mutualInformation_half
-- name    : GeneralCK.Information.mutualInformation_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T19:34:27.251211+00:00
-- url     : https://prove2.me/theorems/51ec72ad-416b-42b1-a134-4f2fa6be940a
-- title:
--   Zero mutual information at crossover probability one half
-- statement:
--   For every $n\in\mathbb N$ and every Boolean function $f:\{0,1\}^n\to\{0,1\}$, $$I(f(X);Y)=0\qquad\text{when }p=\tfrac12.$$ Here $X$ is uniform on the Boolean cube and $Y$ is produced by independently flipping each coordinate with probability one half. The result also includes dimension zero. It verifies the completely noisy case of the Courtade–Kumar inequality: the channel output is independent of the input, hence of every one-bit summary.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/InformationIdentity.lean#L135-L140

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open scoped BigOperators

open GeneralCK

theorem GeneralCK.Information.mutualInformation_half {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f (1 / 2) = 0 := by sorry
