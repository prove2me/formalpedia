-- Prove2me | Theorems.Thm_OAI_Problem313_sqrt_block_cutoff_budget
-- name    : OAI.Problem313.sqrt_block_cutoff_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:56:35.639765+00:00
-- url     : https://prove2.me/theorems/f3cdc469-47a1-46eb-b06c-18146d980677
-- title:
--   The collision budget for square-root blocks
-- statement:
--   Let $n\ge2$ with $\log n\ge16$, $m=\lfloor\sqrt n\rfloor$, $0\le\sigma\le\frac12$ and $k=\sigma\log m/64$. Then
--   $$
--   k^2\,\frac{m-1}{n-1}\le\frac12 .
--   $$
--
--   A support with at most $k^2/2$ edges has at most $k^2$ vertices. A random $m$-block containing one of them meets another with probability at most $\frac12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean#L109-L125

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

theorem OAI.Problem313.sqrt_block_cutoff_budget (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by sorry
