-- Prove2me | Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_switch_to_positive_excess
-- name    : OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T18:57:18.40783+00:00
-- url     : https://prove2.me/theorems/b07a0ca0-4686-4f71-9a01-22c5a8f2c61f
-- title:
--   OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess: intermediate lemma from OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess` of [lean/OAI/Analysis/BiholderTransport/Oscillation/SwitchToExcess.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Oscillation/SwitchToExcess.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakMTWTransport`, with `open Set Filter Manifold Bundle`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma WeakMTW.switch_to_positive_excess (hmtw:WeakMTW (n:=n) (M:=M))
--       {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hd:IsCostDualPair u v)
--       {x:M} {p q:TangentSpace 𝓘(ℝ,Model n) x} (hp:p∈minimizingVectors x) (hq:q∈minimizingVectors x)
--       {α D b r R H eta C d:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo)
--       (ha:v (riemannianExp x p)=α) (ha1:v (riemannianExp x q)=α+D)
--       (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hR:0 ≤ R) (hC:0 ≤ C)
--       (hg0:contactGap u v x (riemannianExp x p) ≤ r)
--       (hg1:contactGap u v x (riemannianExp x q) ≤ r)
--       (hangle:‖p‖^2-inner ℝ p q≤6*D)
--       (heta:0 ≤ eta) (heta1:eta≤1/128) (hrb:r≤b/4) (hbD:b≤D/16)
--       (hob:∀s,0 ≤ Bo s ∧ Bo s≤H) (ho0:Bo 0≤1+1/1024) (ho1:Bo 1=0)
--       (hol:∀s≤1/16,1≤Bo s) (hbar:∀s∈Icc (1/16) (1-eta),Bo 0+1≤Bo s)
--       (hc0:∀s,-1≤Bc s) (hc1:∀s≤1/2,1-1/1024≤Bc s)
--       (hsmall:‖((8*b/D):ℝ) • p‖<d)
--       (hanchor:b*H+2*r+6*D*(8*b/D)+(C*‖p‖^2)*(8*b/D)^2≤R)
--       (hosc:∀z:M,sectionOscillation u v z R≤(1+eta)*D)
--       (hlower:4*eta*D+2*r+12*D*(8*b/D)+2*(C*‖p‖^2)*(8*b/D)^2+b≤D)
--       (hlower':2*(C*‖p‖^2)*(8*b/D)≤2*D)
--       (hnorm:2*(8*b/D)*‖p‖^2+2*b*H+2*r≤D/4)
--       (herror:r+(C+1)*(8*b/D)^2*‖p‖^2≤b/1024)
--       (hTaylor:∀z:M,∀p' w:TangentSpace 𝓘(ℝ,Model n) z,
--         p'∈minimizingVectors z → ‖w‖<d → cost (riemannianExp z w) (riemannianExp z p')≤
--           cost z (riemannianExp z p')-inner ℝ p' w+C*‖w‖^2) :
--       ∃y:M,b / 1024 ≤ modifiedExcess v α D b Bc Bo y
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakMTWTransport.IsCostDualPair`, `OAI.WeakMTWTransport.contactGap` and `OAI.WeakMTWTransport.minimizingVectors` (definitions bundle `OAIQ232A000` of this split); `OAI.WeakMTWTransport.modifiedExcess` (definitions bundle `OAIQ232A007` of this split); `OAI.WeakMTWTransport.sectionOscillation` (definitions bundle `OAIQ232A016` of this split); `OAI.WeakMTWTransport.Model`, `OAI.WeakMTWTransport.WeakMTW`, `OAI.WeakMTWTransport.cost` and `OAI.WeakMTWTransport.riemannianExp` (the published bundle `Def_BiholderTransport`).
--
--   **Used by.** The proof of `OAI.WeakMTWTransport.WeakMTW.class_power` of this split imports it.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Oscillation/SwitchToExcess.lean (declaration OAI.WeakMTWTransport.WeakMTW.switch_to_positive_excess)

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
import Definitions.Def_OAIQ232A016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SwitchToExcess
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.switch_to_positive_excess (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hd:IsCostDualPair u v)
    {x:M} {p q:TangentSpace 𝓘(ℝ,Model n) x} (hp:p∈minimizingVectors x) (hq:q∈minimizingVectors x)
    {α D b r R H eta C d:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo)
    (ha:v (riemannianExp x p)=α) (ha1:v (riemannianExp x q)=α+D)
    (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hR:0 ≤ R) (hC:0 ≤ C)
    (hg0:contactGap u v x (riemannianExp x p) ≤ r)
    (hg1:contactGap u v x (riemannianExp x q) ≤ r)
    (hangle:‖p‖^2-inner ℝ p q≤6*D)
    (heta:0 ≤ eta) (heta1:eta≤1/128) (hrb:r≤b/4) (hbD:b≤D/16)
    (hob:∀s,0 ≤ Bo s ∧ Bo s≤H) (ho0:Bo 0≤1+1/1024) (ho1:Bo 1=0)
    (hol:∀s≤1/16,1≤Bo s) (hbar:∀s∈Icc (1/16) (1-eta),Bo 0+1≤Bo s)
    (hc0:∀s,-1≤Bc s) (hc1:∀s≤1/2,1-1/1024≤Bc s)
    (hsmall:‖((8*b/D):ℝ) • p‖<d)
    (hanchor:b*H+2*r+6*D*(8*b/D)+(C*‖p‖^2)*(8*b/D)^2≤R)
    (hosc:∀z:M,sectionOscillation u v z R≤(1+eta)*D)
    (hlower:4*eta*D+2*r+12*D*(8*b/D)+2*(C*‖p‖^2)*(8*b/D)^2+b≤D)
    (hlower':2*(C*‖p‖^2)*(8*b/D)≤2*D)
    (hnorm:2*(8*b/D)*‖p‖^2+2*b*H+2*r≤D/4)
    (herror:r+(C+1)*(8*b/D)^2*‖p‖^2≤b/1024)
    (hTaylor:∀z:M,∀p' w:TangentSpace 𝓘(ℝ,Model n) z,
      p'∈minimizingVectors z → ‖w‖<d → cost (riemannianExp z w) (riemannianExp z p')≤
        cost z (riemannianExp z p')-inner ℝ p' w+C*‖w‖^2) :
    ∃y:M,b / 1024 ≤ modifiedExcess v α D b Bc Bo y := by
  sorry

end SwitchToExcess
end WeakMTWTransport

end
end

end OAI
end
