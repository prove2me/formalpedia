-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_CenterSequenceData_regular_compact
-- name    : OAI.WeakMTWTransport.CenterSequenceData.regular_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:43:23.521032+00:00
-- url     : https://prove2.me/theorems/e1917c09-34f8-40a3-adc4-d3617be3b1e5
-- title:
--   OAI.WeakMTWTransport.CenterSequenceData.regular_compact: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.CenterSequenceData.regular_compact` of [lean/OAI/Analysis/BiholderTransport/Regularity/CenterRegularCompact.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/CenterRegularCompact.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--   lemma CenterSequenceData.regular_compact {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
--       (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
--       (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
--       {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
--       {F:ℕ → Model n → ℝ}
--       (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
--       {q:Model n}
--       (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
--       (he:riemannianExp a q=c)
--       (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
--       (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
--       (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
--       (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
--       (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
--       (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
--       (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.CenterSequenceData` and `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.injectivityDomain` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proofs of `OAI.WeakMTWTransport.MaximumJensenFamily.center_regular` and `OAI.WeakMTWTransport.exists_maximum_true_center` of this split import it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/CenterRegularCompact.lean (declaration OAI.WeakMTWTransport.CenterSequenceData.regular_compact)

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceRegular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma CenterSequenceData.regular_compact {a c:M} {u v:M → ℝ} {Φ:ℝ×ℝ → ℝ} {γ l:ℝ}
    (hv:Continuous v) (hΦ:ContDiffAt ℝ ∞ Φ (γ,v c))
    (hder:deriv (fun s=>Φ (γ,s)) (v c)=l) (hl:0 < l) (hl1:l < 1)
    {γj lj τj tj:ℕ → ℝ} {xj bj qj:ℕ → Model n} {zj:ℕ → M}
    {F:ℕ → Model n → ℝ}
    (D:CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F)
    {q:Model n}
    (hq:(show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a)
    (he:riemannianExp a q=c)
    (hγ:Tendsto γj atTop (𝓝 γ)) (hlm:Tendsto lj atTop (𝓝 l))
    (hτ:Tendsto τj atTop (𝓝 0)) (ht:Tendsto tj atTop (𝓝 1))
    (hx:Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hb:Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hτpos:∀ᶠ i in atTop,0 < τj i) (L:ℝ≥0)
    (hLip:∀ᶠ i in atTop,LipschitzWith L (fun y=>Φ (γj i,v y))) :
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a := by
  sorry

end CenterSequenceRegular
end WeakMTWTransport

end
end

end OAI
end
