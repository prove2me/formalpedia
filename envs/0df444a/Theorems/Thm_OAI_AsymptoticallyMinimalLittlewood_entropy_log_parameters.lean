-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_entropy_log_parameters
-- name    : OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:42:28.564561+00:00
-- url     : https://prove2.me/theorems/869ce7ae-28c9-45a6-a861-e098fca139f7
-- title:
--   Elementary estimates for the logarithmic parameter $\log(16R/s)$
-- statement:
--   Let $s$ and $R$ be real numbers with $0<s\le R$, and put
--
--   $$
--   L=\log\frac{16R}{s}.
--   $$
--
--   Then the following four inequalities hold:
--
--   1. $L\ge\tfrac12$;
--   2. $e^{-4L}\le\tfrac12$;
--   3. $2R\,e^{-128L}\le\dfrac{s}{512\,L}$;
--   4. $4R\,e^{-4L}\le\dfrac{s}{64}$.
--
--   These are the numerical facts behind the choice of parameters in the partial-coloring argument for an $R\times s$ matrix (with $R$ rows and $s$ columns): (2) is the admissibility condition $e^{-a}\le\tfrac12$ for $a=4L$, while (3) and (4) make the expected rounding cost and the code-counting term small compared with $s$. The constants are generous and not optimized.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L336-L397

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.entropy_log_parameters {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R) :
    let L := Real.log (16 * R / s)
    1 / 2 ≤ L ∧ Real.exp (-4 * L) ≤ 1 / 2 ∧
      2 * R * Real.exp (-128 * L) ≤ s / (512 * L) ∧
      4 * R * Real.exp (-4 * L) ≤ s / 64 := by sorry
