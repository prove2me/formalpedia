-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_int_geometric_sum_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:33:53.859417+00:00
-- url     : https://prove2.me/theorems/c4daaef6-79cb-41a8-a5a1-5822bd91778c
-- title:
--   Two-sided geometric sums over finite sets of integers are at most $e^{4q}$
-- statement:
--   Let $S\subset\mathbb{Z}$ be a finite set of integers and let $q$ be a real number with $0\le q\le\tfrac12$. Then
--
--   $$
--   \sum_{z\in S}q^{|z|}\le e^{4q}.
--   $$
--
--   Here $q^0=1$, also when $q=0$. The bound holds uniformly over all finite $S$, so it is really a bound on the full two-sided geometric series $\sum_{z\in\mathbb{Z}}q^{|z|}=\frac{1+q}{1-q}$. It is the one-dimensional partition-function estimate used to count integer quantization codes: with $q=e^{-a}$ it bounds $\sum_{z}e^{-a|z|}$.
--
--   **Formalization Note** $|z|$ is `Int.natAbs z`, so $q^{|z|}$ is a natural-number power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L129-L153

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.int_geometric_sum_le (S : Finset ℤ) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) :
    (∑ z ∈ S, q ^ z.natAbs) ≤ Real.exp (4 * q) := by sorry
