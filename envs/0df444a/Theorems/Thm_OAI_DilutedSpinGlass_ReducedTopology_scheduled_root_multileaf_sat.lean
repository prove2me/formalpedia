-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_ReducedTopology_scheduled_root_multileaf_sat
-- name    : OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:09.351202+00:00
-- url     : https://prove2.me/theorems/df87f0c7-e184-4beb-933a-501028c2f4f8
-- title:
--   OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf` of [lean/OAI/Probability/DilutedSpin/ScheduledRootMultileaf.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ScheduledRootMultileaf.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.ReducedTopology`, with `open _root_.MeasureTheory`, `open scoped BigOperators`, `open PrescribedTree`):
--
--   ```lean
--   theorem scheduled_root_multileaf_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
--       [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
--       (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
--       (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
--       (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
--       (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
--       (K : (z : Z) → KernelTower (Ω z) (H+1+1+r+1+d))
--       (f : (z : Z) → FinitePath (Ω z) (H+1+1+r+1+d) → Fin N → ℝ)
--       (hf : ∀ z x i, |f z x i|≤1) :
--       let L := H+1+1+r+1+d
--       let ht := shiftedFrameHeight H r d
--       let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
--       let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
--       let OldNode := PrescribedTree.node k OldChild
--       let NewNode := PrescribedTree.node k NewChild
--       let S := splitFrame OldNode r d
--       let RawTarget := splitFrame NewNode (r+1) d
--       let Target := heightCast ht RawTarget
--       let K' := fun z => kernelHeightCast ht.symm (K z)
--       let f' := fun z => vectorHeightCast ht.symm (f z)
--       let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
--       let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
--       let h := fun z => projectionShiftError a C e (K z) (f z) Q
--       let X := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
--       let A := fun z => spatialProduct (fun _ : I => f z)
--       ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
--         ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
--           q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
--       ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
--       ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
--         insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
--       let q := fun j => leafHeightCast ht RawTarget (q0 j)
--       let x := splitFrameLeaf OldNode r d 0 b
--       let y := splitFrameLeaf OldNode r d 1 b
--       let m := grid L 0 L
--       let J := partialKappa Target m (Finset.univ.image q)/
--         partialKappa Target m ((insert v ({u}:Finset I)).image q)
--       Integrable (fun z => shapeEnergyAt (stem OldNode r) d (K z) (f z)) μ →
--       Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
--       Integrable (fun z => matrixObservableHistory Target q (K z) m (v::cs) S x (A z) (treeOverlap S (f z))) μ →
--       Integrable (fun z => matrixProjectionError Target q (K z) u v (A z) (X z)) μ →
--       Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
--       Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
--       Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
--       Integrable (fun z => Real.sqrt (W' z)) μ → Integrable h μ →
--       (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
--         2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (v::cs) x A
--             (fun z => treeOverlap S (f z))|/|J|+
--           (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
--           pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
--         (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.kernelHeightCast`, `OAI.DilutedSpinGlass.vectorHeightCast`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.KernelTower.halfTripleDifferenceAt`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.Sample`, `OAI.DilutedSpinGlass.PrescribedTree.branchingCount`, `OAI.DilutedSpinGlass.PrescribedTree.descendantEnergyAt`, `OAI.DilutedSpinGlass.PrescribedTree.grid`, `OAI.DilutedSpinGlass.PrescribedTree.heightCast`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafHeightCast`, `OAI.DilutedSpinGlass.PrescribedTree.matrixObservableHistory`, `OAI.DilutedSpinGlass.PrescribedTree.matrixProjectionError`, `OAI.DilutedSpinGlass.PrescribedTree.matrixRootCovariance`, `OAI.DilutedSpinGlass.PrescribedTree.oldProjectionError`, `OAI.DilutedSpinGlass.PrescribedTree.pairHistoryMass`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.pathAt`, `OAI.DilutedSpinGlass.PrescribedTree.sampleFintype`, `OAI.DilutedSpinGlass.PrescribedTree.sampleLaw`, `OAI.DilutedSpinGlass.PrescribedTree.shapeEnergyAt`, `OAI.DilutedSpinGlass.PrescribedTree.shiftedCharge`, `OAI.DilutedSpinGlass.PrescribedTree.spatialProduct`, `OAI.DilutedSpinGlass.PrescribedTree.splitFrame`, `OAI.DilutedSpinGlass.PrescribedTree.splitFrameLeaf`, `OAI.DilutedSpinGlass.PrescribedTree.splitProjector`, `OAI.DilutedSpinGlass.PrescribedTree.stem`, `OAI.DilutedSpinGlass.PrescribedTree.treeOverlap`, `OAI.DilutedSpinGlass.ReducedTopology.Vertex`, `OAI.DilutedSpinGlass.ReducedTopology.projectionShiftError`, `OAI.DilutedSpinGlass.ReducedTopology.realize` and `OAI.DilutedSpinGlass.ReducedTopology.shiftedFrameHeight` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ScheduledRootMultileaf.lean (declaration OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf)

import Mathlib
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
open PrescribedTree
variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I] {N : ℕ}

theorem scheduled_root_multileaf_sat {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (K : (z : Z) → KernelTower (Ω z) (H+1+1+r+1+d))
    (f : (z : Z) → FinitePath (Ω z) (H+1+1+r+1+d) → Fin N → ℝ)
    (hf : ∀ z x i, |f z x i|≤1) :
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
    let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let X := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let y := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    Integrable (fun z => shapeEnergyAt (stem OldNode r) d (K z) (f z)) μ →
    Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
    Integrable (fun z => matrixObservableHistory Target q (K z) m (v::cs) S x (A z) (treeOverlap S (f z))) μ →
    Integrable (fun z => matrixProjectionError Target q (K z) u v (A z) (X z)) μ →
    Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
    Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
    Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
    Integrable (fun z => Real.sqrt (W' z)) μ → Integrable h μ →
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  sorry

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end
