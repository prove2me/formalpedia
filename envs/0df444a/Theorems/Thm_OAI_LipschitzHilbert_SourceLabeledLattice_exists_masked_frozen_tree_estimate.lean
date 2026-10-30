-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_masked_frozen_tree_estimate
-- name    : OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:51:00.348027+00:00
-- url     : https://prove2.me/theorems/670bca08-2a94-4b2b-b5f0-453f9f3e32d7
-- title:
--   OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedFrozenEstimate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedFrozenEstimate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLabeledLattice`, with `open Set MeasureTheory`, `open scoped BigOperators FourierTransform`, `open SourceWhitney`):
--
--   ```lean
--   theorem exists_masked_frozen_tree_estimate (hL : LepingleInput)
--       (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
--       ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
--         (∀ j, (P.labels j).card≤B) → 207≤P.order →
--       ∀ (hne : Nonempty P.PacketIndex)
--         (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
--         (a b w eta sigma : ℝ),
--         0<w → 0≤eta → 0 ≤ sigma →
--         (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
--         (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
--         (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
--           |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
--         (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
--         (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
--           |η-P.frequency k|≤Cv/P.width) →
--         (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
--         (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width)≤
--           sigma^2*(P.topLength*P.width) →
--       ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
--       ∀ (Omega : P.DensityWhitneyCell → Set ℝ),
--         (∀ i, MeasurableSet (Omega i)) →
--         (∀ i, ¬P.HasLongPacket i → Omega i=∅) →
--         (∀ i n, (volume.prod volume).real
--           (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
--           32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) →
--         Integrable (P.frozenTreeValueAtWidth w hne c E u Omega) (volume.prod volume) ∧
--         (∫ z, ‖P.frozenTreeValueAtWidth w hne c E u Omega z‖ ∂volume.prod volume)≤
--           Real.sqrt (C*(B:ℝ))*P.absoluteConstant*eta*sigma*(P.topLength*P.width)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.DyadicLineGrid.scale`, `OAI.LipschitzHilbert.SourceLabeledLattice.DensityWhitneyCell`, `OAI.LipschitzHilbert.SourceLabeledLattice.PacketIndex`, `OAI.LipschitzHilbert.SourceLabeledLattice.absoluteConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice.actualX`, `OAI.LipschitzHilbert.SourceLabeledLattice.actualZ`, `OAI.LipschitzHilbert.SourceLabeledLattice.length`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalPacket` and `OAI.LipschitzHilbert.SourceWhitney.Whitney` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.SourceLabeledLattice.HasLongPacket`, `OAI.LipschitzHilbert.SourceLabeledLattice.frozenTreeValueAtWidth` and `OAI.LipschitzHilbert.SourceWhitney.partitionCell` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedFrozenEstimate.lean (declaration OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney

theorem exists_masked_frozen_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (a b w eta sigma : ℝ),
      0<w → 0≤eta → 0 ≤ sigma →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width)≤
        sigma^2*(P.topLength*P.width) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (Omega : P.DensityWhitneyCell → Set ℝ),
      (∀ i, MeasurableSet (Omega i)) →
      (∀ i, ¬P.HasLongPacket i → Omega i=∅) →
      (∀ i n, (volume.prod volume).real
        (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) →
      Integrable (P.frozenTreeValueAtWidth w hne c E u Omega) (volume.prod volume) ∧
      (∫ z, ‖P.frozenTreeValueAtWidth w hne c E u Omega z‖ ∂volume.prod volume)≤
        Real.sqrt (C*(B:ℝ))*P.absoluteConstant*eta*sigma*(P.topLength*P.width) := by
  sorry

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end
