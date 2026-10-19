-- Prove2me | Theorems.Thm_OAI_LittlewoodFiniteFlatness_tendsto_integral_rpow_of_bounded_moment
-- name    : OAI.LittlewoodFiniteFlatness.tendsto_integral_rpow_of_bounded_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:40:30.567351+00:00
-- url     : https://prove2.me/theorems/0b166640-2ae3-4a7d-9462-d79ec703fb41
-- title:
--   One vanishing moment of bounded functions gives all moments
-- statement:
--   Let $\mu$ be a probability measure and $g_n$ measurable functions with $0\le g_n\le1$ for all large $n$. If for some integer $k\ge1$
--   $$
--   \int g_n^k\,d\mu\to0,
--   $$
--   then $\int g_n^p\,d\mu\to0$ for every real $p>0$.
--
--   For uniformly bounded functions, convergence to zero in one $L^k$ norm implies convergence in every $L^p$ norm. No pointwise convergence is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/Integral/BoundedMoments.lean#L27-L72

import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily

open OAI
open Filter MeasureTheory
open scoped Topology

theorem OAI.LittlewoodFiniteFlatness.tendsto_integral_rpow_of_bounded_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : ℕ → α → ℝ) (hg : ∀ n, Measurable (g n))
    (hb : ∀ᶠ n in atTop, ∀ x, 0 ≤ g n x ∧ g n x ≤ 1)
    (k : ℕ) (_hk : 0 < k)
    (hmoment : Tendsto (fun n => ∫ x, g n x ^ k ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, g n x ^ p ∂μ) atTop (𝓝 0) := by sorry
