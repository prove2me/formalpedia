-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_bool_exp_sum_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:30:35.325984+00:00
-- url     : https://prove2.me/theorems/b81ce8b7-8eab-4af0-8599-741ef1b48104
-- title:
--   Exponential moment of a bounded coefficient times a random sign
-- statement:
--   Let $\sigma\colon\{\mathrm{true},\mathrm{false}\}\to\{-1,1\}$ denote the sign encoding $\sigma(\mathrm{true})=1$, $\sigma(\mathrm{false})=-1$. For every real number $a$ with $|a|\le 1$ and every real number $t$,
--
--   $$
--   \sum_{b\in\{\mathrm{true},\mathrm{false}\}} e^{\,t a\,\sigma(b)}=e^{ta}+e^{-ta}\le 2\,e^{t^2/2}.
--   $$
--
--   Equivalently, if $\varepsilon$ is a uniformly random sign, then $\mathbb{E}\,e^{t a\varepsilon}\le e^{t^2/2}$: a bounded multiple of a Rademacher variable is sub-Gaussian with variance proxy $1$. This one-coordinate estimate is the building block for exponential-moment bounds of randomly signed sums.
--
--   **Formalization Note** Signs are encoded by Booleans through `boolSign b = if b then 1 else -1`, and the expectation is written as a sum over the two values of `Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L18-L32

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.bool_exp_sum_le {a : ℝ} (ha : |a| ≤ 1) (t : ℝ) :
    (∑ b : Bool, Real.exp (t * a * boolSign b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by sorry
