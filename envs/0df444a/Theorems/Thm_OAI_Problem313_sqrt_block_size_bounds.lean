-- Prove2me | Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds
-- name    : OAI.Problem313.sqrt_block_size_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:46:34.762841+00:00
-- url     : https://prove2.me/theorems/f8f9e22a-4001-4ed2-bde3-7ef05af458a0
-- title:
--   Size of the square-root vertex block
-- statement:
--   Let $n\ge2$ with $\log n\ge16$, and $m=\lfloor\sqrt n\rfloor$. Then
--   $$
--   3\le m\le n,\qquad\frac{\sqrt n}2\le m .
--   $$
--
--   The random vertex blocks used in the proof have about $\sqrt n$ vertices. These bounds make that precise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockSize.lean#L14-L31

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit

open OAI OAI.Problem313

theorem OAI.Problem313.sqrt_block_size_bounds (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    3 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ ∧
      ⌊Real.sqrt (n : ℝ)⌋₊ ≤ n ∧
      Real.sqrt (n : ℝ) / 2 ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by sorry
