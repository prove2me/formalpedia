-- Prove2me | Theorems.Thm_MeasureTheory_exists_holder_representative_of_ae_tendsto
-- name    : MeasureTheory.exists_holder_representative_of_ae_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:21:32.578999+00:00
-- url     : https://prove2.me/theorems/e7386834-a333-40c6-bedd-5f947d80a524
-- title:
--   A.e. limits with a common Hölder bound have a continuous representative
-- statement:
--   Let $X$ and $Y$ be metric spaces with $Y$ complete, and let $\mu$ be a measure on $X$ that is positive on every nonempty open set. Suppose $v_j:X\to Y$ converges almost everywhere to $f$, and for fixed $K\ge0$ and $\alpha>0$ every $v_j$ satisfies $d(v_j(x),v_j(y))\le Kd(x,y)^\alpha$. Then $f$ has a continuous representative with the same Hölder bound. No measurability or continuity assumption on the approximating functions is required. The proof takes limits on the conull dense set and extends uniformly continuously.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68–70, Theorems 3.36–3.37; homogeneous mollification and dense-set extension in the proof of Theorem 3.37.

import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

theorem MeasureTheory.exists_holder_representative_of_ae_tendsto {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (K : ℝ≥0) (α : ℝ) (hα : 0 < α) (v : ℕ → X → Y) (f : X → Y)
    (hv : ∀ j x y, dist (v j x) (v j y) ≤ (K : ℝ) * dist x y ^ α)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun j => v j x) atTop (𝓝 (f x))) :
    ∃ u : X → Y, Continuous u ∧ u =ᵐ[μ] f ∧
      ∀ x y, dist (u x) (u y) ≤ (K : ℝ) * dist x y ^ α := by sorry
