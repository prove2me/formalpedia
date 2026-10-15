-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_log_factorial_upper
-- name    : OAI.ThorpCompatibility.log_factorial_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:41:44.705375+00:00
-- url     : https://prove2.me/theorems/c9173ea6-91a1-47af-b21e-acc52e16c9f3
-- title:
--   Explicit upper bound $\log n!\le n\log n-n+1+\log n$
-- statement:
--   For every integer $n\ge 1$,
--
--   $$
--   \log n!\;\le\; n\log n-n+1+\log n ,
--   $$
--
--   where $\log$ is the natural logarithm. Exponentiating, this is the elementary Stirling-type estimate $n!\le e\,n^{n+1}e^{-n}$.
--
--   Compared with Stirling's formula $\log n!=n\log n-n+\tfrac12\log(2\pi n)+o(1)$, the bound is off by only about $\tfrac12\log n$, and it holds for every $n\ge1$ with fully explicit constants. It is used to bound from below the average of the logarithmic rank terms $\log\frac{D}{D-t}$, $0\le t<D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/LogEstimates.lean#L41-L56

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.log_factorial_upper (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by sorry
