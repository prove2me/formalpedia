-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_theorem_2_7
-- name    : LowRandomnessDP.KNorm.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:23.41173+00:00
-- url     : https://prove2.me/theorems/1a747167-984a-48f0-a263-a31734eda2b4
-- title:
--   Theorem 2.7 — countable exponential mechanism privacy
-- statement:
--   Let $D$ carry any symmetric adjacency relation. Let $I$ be finite or countably infinite, and let $s_x(i)$ be real scores with $|s_x(i)-s_y(i)|\le1$ for adjacent $x,y$. For $\varepsilon>0$, suppose each full exponential normalizer is positive and finite. Given any output map $r:I\to O$ into a measurable space, the atomic output law
--
--   $$M_x=\sum_{i\in I}\frac{e^{-\varepsilon s_x(i)/2}}{\sum_j e^{-\varepsilon s_x(j)/2}}\,\delta_{r(i)}$$
--
--   is a probability measure and is $\varepsilon$-differentially private on all measurable events. This is the privacy interface for Algorithm 2.
--
--   Differences from the source:
--   - generalization: finite datasets X* → an arbitrary dataset type D with a symmetric adjacency relation; reason: specializes to D=List X with every source neighboring relation; no input measurability is imposed
--   - encoding: a well-defined atomic exponential mechanism on an output set → a countable index set and finite positive extended normalizer; reason: strictly positive summable weights force countable output; normalization is the meaning of a probability mechanism
--   - generalization: output the sampled label → also allow an arbitrary deterministic output map into a measurable space; reason: the identity map recovers the source and deterministic postprocessing preserves the event inequality
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Theorem 2.7, PDF page 8 / printed page 6

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem theorem_2_7 {D ι O : Type} [Countable ι] [MeasurableSpace O]
    (adj : D → D → Prop) (hadj : Std.Symm adj) (ε : ℝ) (hε : 0 < ε)
    (score : D → ι → ℝ) (out : ι → O)
    (hsens : ∀ x y, adj x y → ∀ i, |score x i - score y i| ≤ 1)
    (hnorm : ∀ x, Normalizable ε (score x)) :
    (∀ x, IsProbabilityMeasure (gibbsMeasure ε (score x) out)) ∧
    PureDP adj ε (fun x => gibbsMeasure ε (score x) out) := by sorry

end LowRandomnessDP.KNorm
