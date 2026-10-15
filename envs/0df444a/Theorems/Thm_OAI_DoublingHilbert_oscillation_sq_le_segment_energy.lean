-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_oscillation_sq_le_segment_energy
-- name    : OAI.DoublingHilbert.oscillation_sq_le_segment_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:28:24.594154+00:00
-- url     : https://prove2.me/theorems/7315925f-e75d-4ad2-9e6e-f4ac8e4358ea
-- title:
--   Squared oscillation on an interval is at most $|I|^2$ times the mean-square derivative
-- statement:
--   Let $E$ be a real Banach space and $I=[\alpha,\beta]$ an interval with $\alpha<\beta$ and length $|I|=\beta-\alpha$. Let $g:\mathbb{R}\to E$ be bounded and strongly measurable, and let $f:\mathbb{R}\to E$ satisfy the fundamental theorem of calculus on every interval:
--   $$\int_a^bg(x)\,dx=f(b)-f(a)\qquad\text{for all }a,b\in\mathbb{R}.$$
--   Then for all $a,b\in[\alpha,\beta]$
--
--   $$
--   \|f(b)-f(a)\|^2\le|I|^2\cdot\frac{1}{|I|}\int_\alpha^\beta\|g(x)\|^2\,dx=|I|\int_\alpha^\beta\|g(x)\|^2\,dx .
--   $$
--
--   The middle expression is $|I|^2$ times the mean of $\|g\|^2$ over $I$. Because the integral identity is assumed on all intervals, the bound holds at every pair of points of the closed interval, not only almost everywhere. It converts a small mean-square derivative along a segment into a uniform bound on the oscillation of $f$ along that segment; this is how a difference of two sheets is shown to be nearly constant along a row or a column of a period block.
--
--   **Formalization Note** The left integral in the hypothesis is the oriented interval integral `∫ x in a..b, g x`, and the mean of $\|g\|^2$ is the integral against `I.law`, the uniform probability measure on $(\alpha,\beta]$. Boundedness and strong measurability of $g$ are the hypothesis `IsBoundedField g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Grids.lean#L238-L279

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter

theorem OAI.DoublingHilbert.oscillation_sq_le_segment_energy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (I : Segment) {f g : ℝ → E}
    (hg : IsBoundedField g)
    (hFTC : ∀ a b, (∫ x in a..b, g x) = f b - f a)
    {a b : ℝ} (ha : a ∈ Icc I.lo I.hi) (hb : b ∈ Icc I.lo I.hi) :
    ‖f b - f a‖ ^ 2 ≤ I.length ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂I.law) := by sorry
