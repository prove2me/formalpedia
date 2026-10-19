-- Prove2me | Theorems.Thm_OAI_Problem313_sqrt_block_detection_probability
-- name    : OAI.Problem313.sqrt_block_detection_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:57:32.983075+00:00
-- url     : https://prove2.me/theorems/0fcb49b1-e40b-4f1a-961f-509863a33a92
-- title:
--   Square-root blocks detect small supports with probability $\ge m/2n$
-- statement:
--   Let $n\ge2$ with $\log n\ge16$, $m=\lfloor\sqrt n\rfloor$, $0\le\sigma\le\frac12$ and $k=\sigma\log m/64$. Let $S$ be a nonempty set of graph edges with $|S|\le k^2/2$. Then a uniformly random $m$-subset $B$ of the vertices detects $S$ at cutoff $k$, i.e. $1\le|\{e\in S:e\cap B\ne\emptyset\}|\le k$, with probability
--   $$
--   \Pr_B[B\text{ detects }S]\ge\frac m{2n} .
--   $$
--
--   Every low-degree Fourier support is seen by a random block with probability comparable to $m/n$. This lets the low-level Fourier mass be transferred to restrictions to blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean#L127-L158

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture

open OAI OAI.Problem313

theorem OAI.Problem313.sqrt_block_detection_probability (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2)
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      blockProbability (Finset.univ : Finset (Fin n)) ⌊Real.sqrt (n : ℝ)⌋₊
        (BlockDetects (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S) := by sorry
