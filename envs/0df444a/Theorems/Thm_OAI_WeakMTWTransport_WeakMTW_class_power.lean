-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_class_power
-- name    : OAI.WeakMTWTransport.WeakMTW.class_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:32.072361+00:00
-- url     : https://prove2.me/theorems/1abeb8b6-6be0-4c55-9283-41d0c55b7a4f
-- title:
--   OAI.WeakMTWTransport.WeakMTW.class_power: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.class_power` of [lean/OAI/Analysis/BiholderTransport/Oscillation/ClassPower.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Oscillation/ClassPower.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter MeasureTheory Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.class_power (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n)
--       {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) (x0:M)
--       (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty) :
--       HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasPowerUpperBound` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.classOscillation` and `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.uniform_biHolder_transport` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Oscillation/ClassPower.lean (declaration OAI.WeakMTWTransport.WeakMTW.class_power)

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
import Definitions.Def_OAIQ232A017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ClassPower
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.class_power (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n)
    {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) (x0:M)
    (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty) :
    HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0) := by
  sorry

end ClassPower
end WeakMTWTransport

end
end

end OAI
end
