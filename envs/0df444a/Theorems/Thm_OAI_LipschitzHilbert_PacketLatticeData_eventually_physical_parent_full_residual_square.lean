-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_physical_parent_full_residual_square
-- name    : OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:40:09.266321+00:00
-- url     : https://prove2.me/theorems/5351c37b-ba5e-494c-8c3c-e99b2c5397bb
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square` of [lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataParentFullResidual.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataParentFullResidual.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem eventually_physical_parent_full_residual_square
--       (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (K H : ℕ) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
--         (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--           (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
--       ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
--         (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
--       ∀ (v : ℝ×ℝ → ℝ), Measurable v →
--       ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
--       ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
--         (T : τ → SlopeBox) (A s w R C F pathSlope : ℝ) (hw : 0 < w) (hR : 0 < R)
--         (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
--         (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
--         (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
--         (grid.branching:ℝ) = SourceParameters.step L →
--       ∀ (hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
--         (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
--           (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
--       let cut := grid.rootWidth/(SourceParameters.branching L)^2
--       let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
--       let weight := fun top z => (T top).weight (L^(A+2)) D z
--       let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
--       ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
--       ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
--       ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
--         (∀ u ∈ packets, assigned u ∈ tops) →
--         (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
--         (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
--       let cone := C+(SourceParameters.branching L)^3
--       let S := sourceReferencePackets packets (fun u => P.length u.1)
--         (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
--       let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
--       let orig := P.referenceOriginalLabel t pathSlope R cone w
--       let selected := (Finset.univ : Finset Q.PacketIndex).filter
--         (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
--       z ∉ (Q.restrictPackets selected).physicalReferenceBad
--         (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
--         (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
--           (fun j l => hAlt j (orig j l)) selected)
--         pathSlope a (fun j l => b j (orig j l)) v f
--         (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
--       let value := P.physicalMaskedValue alt hAlt t b v f
--         (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
--       (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
--         (fun u => stop u.1)
--         (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
--         (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
--           (grid.sourceBoundaryGap L) phase z)
--         (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
--         (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
--           (L^(3*q+13))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.sourceReferencePackets`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.firstIneligibleShiftedBlock`, `OAI.LipschitzHilbert.AngularGrid.index`, `OAI.LipschitzHilbert.AngularGrid.lastEligible`, `OAI.LipschitzHilbert.AngularGrid.packetResidual`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryGap`, `OAI.LipschitzHilbert.AngularGrid.sourcePacketBase`, `OAI.LipschitzHilbert.AngularGrid.sourceTransition`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.length_pos`, `OAI.LipschitzHilbert.PacketLatticeData.physicalMaskedValue`, `OAI.LipschitzHilbert.PacketLatticeData.referenceEnvelopeConstant`, `OAI.LipschitzHilbert.PacketLatticeData.referenceFamily`, `OAI.LipschitzHilbert.PacketLatticeData.referenceLabels`, `OAI.LipschitzHilbert.PacketLatticeData.referenceOriginalLabel`, `OAI.LipschitzHilbert.ShiftedBlocks.endpoint`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.PacketIndex`, `OAI.LipschitzHilbert.SourceLabeledLattice.RestrictedPacketItem`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalReferenceBad`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictPackets`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedAlternate`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedAlternate_bound`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.branching`, `OAI.LipschitzHilbert.SourceParameters.step` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataParentFullResidual.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000

section

attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_full_residual_square
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (K H : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ K) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s w R C F pathSlope : ℝ) (hw : 0 < w) (hR : 0 < R)
      (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hKb shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let cone := C+(SourceParameters.branching L)^3
    let S := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
    let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t pathSlope R cone w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      pathSlope a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+13))^2 := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
