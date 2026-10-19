-- Prove2me | Theorems.Thm_OAI_Problem313_block_capture_exp_lower
-- name    : OAI.Problem313.block_capture_exp_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:47:01.187038+00:00
-- url     : https://prove2.me/theorems/3d12e45e-7774-4e54-a4e8-424e2a26063c
-- title:
--   An exponential lower bound for $t\ge16$
-- statement:
--   For every real $t\ge16$,
--   $$
--   2t^2\le e^{t/2} .
--   $$
--
--   With $t=\log n$ this gives $(\log n)^2\le\sqrt n/2$. That bound controls collisions of a random block with a small support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockSize.lean#L63-L84

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit

open OAI OAI.Problem313

theorem OAI.Problem313.block_capture_exp_lower (t : ℝ) (ht : 16 ≤ t) :
    2 * t ^ 2 ≤ Real.exp (t / 2) := by sorry
