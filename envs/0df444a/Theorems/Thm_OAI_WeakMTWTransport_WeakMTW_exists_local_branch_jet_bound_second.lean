-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_local_branch_jet_bound_second
-- name    : OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:02:14.405146+00:00
-- url     : https://prove2.me/theorems/62a08ecc-9b87-49ed-81d4-541b9a5b3e6e
-- title:
--   OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second` of [lean/OAI/Analysis/BiholderTransport/CostGeometry/BranchJetSecond.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/CostGeometry/BranchJetSecond.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff BoundedContinuousFunction`):
--
--   ```lean
--   lemma WeakMTW.exists_local_branch_jet_bound_second (hmtw:WeakMTW (n := n) (M := M))
--       {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
--       {r:TangentSpace 𝓘(ℝ,Model n) a} (hr:r∈minimizingVectors a)
--       {G:M×M → ℝ}
--       (hG:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (a,riemannianExp a r))
--       (hagree:∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),
--         z.2∈injectivityDomain z.1 → (fun q:M×M=>cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
--       {l:ℝ} (hl:1 < l) :
--       let d:=extChartAt 𝓘(ℝ,Model n) a
--       ∃ U:Set ((Model n×M)×ℝ),U∈𝓝 ((d a,riemannianExp a r),l) ∧ ∃ C≥0,
--         ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
--         uv∈densityDualClass (metricVolume n) lam cap x0 →
--         ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (d.symm q.1.1)) →
--         HasDerivAt φ q.2 (uv.2 (d.symm q.1.1)) →
--         iteratedDeriv 2 φ (uv.2 (d.symm q.1.1)) ≤ 0 →
--         ∀H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀w,0 ≤ H w w) →
--         HasLowerSecondTaylor (fun w=>φ (uv.2 (d.symm (q.1.1+w)))+G (d.symm (q.1.1+w),q.1.2)) 0 H →
--         ∀w,H w w ≤ C*‖w‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.HasLowerSecondTaylor` and `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.densityDualClass` (definitions bundle `OAIQ232A017` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.cost`, `OAI.WeakMTWTransport.injectivityDomain`, `OAI.WeakMTWTransport.metricVolume` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/CostGeometry/BranchJetSecond.lean (declaration OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second)

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
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section BranchJetSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_branch_jet_bound_second (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
    {r:TangentSpace 𝓘(ℝ,Model n) a} (hr:r∈minimizingVectors a)
    {G:M×M → ℝ}
    (hG:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (a,riemannianExp a r))
    (hagree:∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 → (fun q:M×M=>cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl:1 < l) :
    let d:=extChartAt 𝓘(ℝ,Model n) a
    ∃ U:Set ((Model n×M)×ℝ),U∈𝓝 ((d a,riemannianExp a r),l) ∧ ∃ C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (d.symm q.1.1)) →
      HasDerivAt φ q.2 (uv.2 (d.symm q.1.1)) →
      iteratedDeriv 2 φ (uv.2 (d.symm q.1.1)) ≤ 0 →
      ∀H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀w,0 ≤ H w w) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (d.symm (q.1.1+w)))+G (d.symm (q.1.1+w),q.1.2)) 0 H →
      ∀w,H w w ≤ C*‖w‖^2 := by
  sorry

end BranchJetSecond
end WeakMTWTransport

end
end

end OAI
end
