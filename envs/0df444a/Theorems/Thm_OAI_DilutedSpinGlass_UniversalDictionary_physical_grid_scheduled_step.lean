-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physical_grid_scheduled_step
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:58:52.790762+00:00
-- url     : https://prove2.me/theorems/e37a4a45-fa9c-4a41-bc2c-f89ccbff1963
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalScheduledStep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalScheduledStep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   theorem physical_grid_scheduled_step (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
--       (u : Spec (H+1+1+r+1+d) × ℕ → ℝ)
--       (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
--       (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
--       (Q : α → Fin (H+1+1+r+1+(d+1))) (ha : (Q a).val=r+1+(d+1))
--       (had : ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) (r+1+(d+1)+1) (r+1+(d+1)+1+H))
--       {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+(d+1):ℕ)) (hr : DepthAverage.Regular η Q) :
--       let L₀ := H+1+1+r+1+d
--       let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
--         (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)
--       let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
--         (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
--         (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
--       let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
--         (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
--       let ht := shiftedFrameHeight H r (d+1)
--       let OldChild := fun j => realize (H+1) (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val)
--       let NewChild := fun j => realize H (r+1+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val+1)
--       let OldNode := PrescribedTree.node k OldChild
--       let NewNode := PrescribedTree.node k NewChild
--       let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val))
--       let B := shiftedPrefixDepths (stem BaseNode r) (d+1)
--       let S := splitFrame OldNode r (d+1)
--       let RawTarget := splitFrame NewNode (r+1) (d+1)
--       let Target := heightCast ht RawTarget
--       let _ := fun z => kernelHeightCast ht.symm (K z)
--       let _ := fun z => vectorHeightCast ht.symm (f z)
--       let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+(d+1)) (C j) (fun v => (Q (e j v)).val) (K z) (f z) ∂μ)
--       let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+1+(d+1)) (C j) (fun v => (Q (e j v)).val+1) (K z) (f z) ∂μ)
--       let h := fun z => projectionShiftError a C e (K z) (f z) Q
--       ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
--         Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) (d+1) 0 b' →
--           q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) (d+1) 1 b' →
--       let v := some (Fin.last t)
--       let cs := canonicalMatrixTail t
--       let q := fun j => leafHeightCast ht RawTarget (q0 j)
--       let x := splitFrameLeaf OldNode r (d+1) 0 b
--       let m := Fin.cons 0 (gridExponents L₀)
--       let J := partialKappa Target m (Finset.univ.image q)/
--         partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
--       ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C) (rootSchedule (r+1+(d+1)) (fun j v => (Q (e j v)).val)) (K z) (f z) ∂μ) ≤
--         2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
--           (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
--           pairHistoryMass S m x*(2*Real.sqrt W))+
--         ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.FullRootState`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.PrescribedTree`, `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.fullRootLaw`, `OAI.DilutedSpinGlass.kernelHeightCast`, `OAI.DilutedSpinGlass.rootArray`, `OAI.DilutedSpinGlass.rootPathMeasurable`, `OAI.DilutedSpinGlass.scoreRate`, `OAI.DilutedSpinGlass.vectorHeightCast`, `OAI.DilutedSpinGlass.ConcreteReservoir.Bond`, `OAI.DilutedSpinGlass.ConcreteReservoir.Site`, `OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw`, `OAI.DilutedSpinGlass.ConcreteReservoir.markLaw`, `OAI.DilutedSpinGlass.ConcreteReservoir.observableAt`, `OAI.DilutedSpinGlass.ConcreteReservoir.physicalBase`, `OAI.DilutedSpinGlass.ConcreteReservoir.readSpin`, `OAI.DilutedSpinGlass.DepthAverage.Regular`, `OAI.DilutedSpinGlass.FiniteLaw.uniform`, `OAI.DilutedSpinGlass.HeterogeneousMarks.Row`, `OAI.DilutedSpinGlass.HeterogeneousMarks.dictionaryFactor`, `OAI.DilutedSpinGlass.HeterogeneousMarks.rootAlphabet`, `OAI.DilutedSpinGlass.HeterogeneousMarks.rootTower`, `OAI.DilutedSpinGlass.HeterogeneousMarks.rootVector`, `OAI.DilutedSpinGlass.KernelTower.terminalState`, `OAI.DilutedSpinGlass.KernelTower.terminalTower`, `OAI.DilutedSpinGlass.PrescribedTree.Leaf`, `OAI.DilutedSpinGlass.PrescribedTree.canonicalMatrixTail`, `OAI.DilutedSpinGlass.PrescribedTree.heightCast`, `OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq`, `OAI.DilutedSpinGlass.PrescribedTree.leafHeightCast`, `OAI.DilutedSpinGlass.PrescribedTree.pairHistoryMass`, `OAI.DilutedSpinGlass.PrescribedTree.partialKappa`, `OAI.DilutedSpinGlass.PrescribedTree.shiftedCharge`, `OAI.DilutedSpinGlass.PrescribedTree.shiftedPrefixDepths`, `OAI.DilutedSpinGlass.PrescribedTree.splitFrame`, `OAI.DilutedSpinGlass.PrescribedTree.splitFrameLeaf`, `OAI.DilutedSpinGlass.PrescribedTree.stem`, `OAI.DilutedSpinGlass.ReducedTopology.Admissible`, `OAI.DilutedSpinGlass.ReducedTopology.Vertex`, `OAI.DilutedSpinGlass.ReducedTopology.projectionShiftError`, `OAI.DilutedSpinGlass.ReducedTopology.realize`, `OAI.DilutedSpinGlass.ReducedTopology.rootSchedule`, `OAI.DilutedSpinGlass.ReducedTopology.scheduledShapeEnergy`, `OAI.DilutedSpinGlass.ReducedTopology.shiftedFrameHeight`, `OAI.DilutedSpinGlass.UniversalDictionary.Alphabet`, `OAI.DilutedSpinGlass.UniversalDictionary.Labels`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.Table`, `OAI.DilutedSpinGlass.UniversalDictionary.anchor`, `OAI.DilutedSpinGlass.UniversalDictionary.direction`, `OAI.DilutedSpinGlass.UniversalDictionary.gridExponents`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalTreeMatrixCovariance`, `OAI.DilutedSpinGlass.UniversalDictionary.prior`, `OAI.DilutedSpinGlass.UniversalDictionary.readVector`, `OAI.DilutedSpinGlass.UniversalDictionary.specMeasurable` and `OAI.DilutedSpinGlass.UniversalDictionary.weights` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proofs of `OAI_DilutedSpinGlass_UniversalDictionary_physicalOverlapLimsup_tendsto` and `OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup_tendsto` of this split import it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalScheduledStep.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {p t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

theorem physical_grid_scheduled_step (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
    (u : Spec (H+1+1+r+1+d) × ℕ → ℝ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+(d+1))) (ha : (Q a).val=r+1+(d+1))
    (had : ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) (r+1+(d+1)+1) (r+1+(d+1)+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+(d+1):ℕ)) (hr : DepthAverage.Regular η Q) :
    let L₀ := H+1+1+r+1+d
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
      (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
      (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    let ht := shiftedFrameHeight H r (d+1)
    let OldChild := fun j => realize (H+1) (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) (d+1)
    let S := splitFrame OldNode r (d+1)
    let RawTarget := splitFrame NewNode (r+1) (d+1)
    let Target := heightCast ht RawTarget
    let _ := fun z => kernelHeightCast ht.symm (K z)
    let _ := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+(d+1)) (C j) (fun v => (Q (e j v)).val) (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+1+(d+1)) (C j) (fun v => (Q (e j v)).val+1) (K z) (f z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) (d+1) 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) (d+1) 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r (d+1) 0 b
    let m := Fin.cons 0 (gridExponents L₀)
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C) (rootSchedule (r+1+(d+1)) (fun j v => (Q (e j v)).val)) (K z) (f z) ∂μ) ≤
      2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W) := by
  sorry

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end
