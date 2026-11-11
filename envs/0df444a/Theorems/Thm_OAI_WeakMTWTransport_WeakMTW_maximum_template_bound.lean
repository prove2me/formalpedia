-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_maximum_template_bound
-- name    : OAI.WeakMTWTransport.WeakMTW.maximum_template_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:59:39.866193+00:00
-- url     : https://prove2.me/theorems/cc5648d6-9718-4a05-9761-01561e96ede8
-- title:
--   OAI.WeakMTWTransport.WeakMTW.maximum_template_bound: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound` of [lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTemplateBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTemplateBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle Metric MeasureTheory`, `open scoped Topology ContDiff NNReal BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.maximum_template_bound (hmtw:WeakMTW (n:=n) (M:=M))
--       (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) :
--       ∃B:ℝ,0 < B ∧ ∃eps:ℝ,0 < eps ∧
--       ∀K eta:ℝ,1 ≤ K → 0 < eta → eta ≤ 1/128 →
--       (let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
--        eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) →
--       ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
--       ∀α D bm bp:ℝ,0 < D → 0 < bm → 0 < bp →
--       bp/D*centerGamma ≤ 1 → bp/D*centerGamma/2 < eps →
--       ∀C:ℝ,0 ≤ C →
--         (∀s,|deriv (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) s| ≤ C) →
--         bp/D*C ≤ 1/2 →
--       (∀z:M,sectionOscillation uv.1 uv.2 z
--         ((2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp) ≤ (1+eta)*D) →
--       2*(2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp ≤ eta*D →
--       MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate
--         (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) →
--       (((1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)))^(n-1)*K/(8*centerGamma^2)) ≤ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.centerGamma`, `OAI.WeakMTWTransport.centerTemplate`, `OAI.WeakMTWTransport.outerTemplate` and `OAI.WeakMTWTransport.templateEps` (definitions bundle `OAIQ232A005` of this split); `OAI.WeakMTWTransport.MaximumFamily` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.sectionOscillation` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW` and `OAI.WeakMTWTransport.metricVolume` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.class_power` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumTemplateBound.lean (declaration OAI.WeakMTWTransport.WeakMTW.maximum_template_bound)

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
open Set Filter Manifold Bundle Metric MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section MaximumTemplateBound
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance templateDualGroup_re9d32b_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance templateDualSpace_re9d32b_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearGroup_re9d32b_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance templateBilinearSpace_re9d32b_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
lemma WeakMTW.maximum_template_bound (hmtw:WeakMTW (n:=n) (M:=M))
    (hn:0 < n) {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) :
    ∃B:ℝ,0 < B ∧ ∃eps:ℝ,0 < eps ∧
    ∀K eta:ℝ,1 ≤ K → 0 < eta → eta ≤ 1/128 →
    (let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
     eta ≤ templateEps/(24*(128*(M0+3)*(K+1)))) →
    ∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),uv∈densityDualClass (metricVolume n) lam cap x0 →
    ∀α D bm bp:ℝ,0 < D → 0 < bm → 0 < bp →
    bp/D*centerGamma ≤ 1 → bp/D*centerGamma/2 < eps →
    ∀C:ℝ,0 ≤ C →
      (∀s,|deriv (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) s| ≤ C) →
      bp/D*C ≤ 1/2 →
    (∀z:M,sectionOscillation uv.1 uv.2 z
      ((2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp) ≤ (1+eta)*D) →
    2*(2*(12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096))+10)*bp ≤ eta*D →
    MaximumFamily (n:=n) uv.2 α D bm bp centerTemplate
      (outerTemplate (12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)) K eta) →
    (((1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ)))^(n-1)*K/(8*centerGamma^2)) ≤ B := by
  sorry

end MaximumTemplateBound
end WeakMTWTransport

end
end

end OAI
end
