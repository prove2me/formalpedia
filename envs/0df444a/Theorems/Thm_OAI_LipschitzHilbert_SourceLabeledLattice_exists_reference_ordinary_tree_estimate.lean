-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_reference_ordinary_tree_estimate
-- name    : OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:52:42.461175+00:00
-- url     : https://prove2.me/theorems/196d22d0-ed08-4652-89bc-ec9308364568
-- title:
--   OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceOrdinaryTree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceOrdinaryTree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLabeledLattice`, with `open Set MeasureTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem exists_reference_ordinary_tree_estimate (hL : LepingleInput)
--       (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
--       ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : SourceLabeledLattice N κ Label Item) (B K : ℕ),
--         (∀ j, (P.labels j).card≤B) → 207≤P.order →
--       ∀ (_hne : Nonempty P.PacketIndex)
--         (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
--         (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
--         0<w → P.topLength≤tau → 0≤Lip → 0≤eta → 0 ≤ sigma →
--         1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
--         (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
--         (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
--         (∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength)
--           grid q.1.val (cell q.1 q.2.1)) →
--         (∀ j l, t+P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
--         (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
--           |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
--         (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
--         (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
--           |η-P.frequency k|≤Cv/P.width) →
--         (∀ j l v, ‖c j l v‖ ≤ sigma) →
--         P.angularSeparatedTreeEnergy cb w c ≤ sigma^2*(P.topLength*P.width) →
--       ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (selector j l k)) →
--         (∀ j l k s, ‖selector j l k s‖≤1) →
--         (∀ j l k, selector j l k t≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
--         (∀ j l k s, selector j l k s≠0 →
--           s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
--         (∀ j l k s, selector j l k s≠0 →
--           |s-(t+P.rowSlope j l)| ≤ radius*(w/P.length j)) →
--         (∀ j l k s, |s-t|≤w/P.length j →
--           ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
--       ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
--         (∀ q, P.ordinaryDensity t cell grid w tau E u q≤eta) →
--         let F := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
--         IntegrableOn F E (volume.prod volume) ∧
--           (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
--             P.ordinaryTreeConstant C B K Lip*sigma*eta*P.topLength*P.width
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.scaledAngularCell`, `OAI.LipschitzHilbert.SourceLabeledLattice.PacketIndex`, `OAI.LipschitzHilbert.SourceLabeledLattice.actualX`, `OAI.LipschitzHilbert.SourceLabeledLattice.actualZ`, `OAI.LipschitzHilbert.SourceLabeledLattice.length` and `OAI.LipschitzHilbert.SourceLabeledLattice.physicalPacket` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.SourceLabeledLattice.angularSeparatedTreeEnergy`, `OAI.LipschitzHilbert.SourceLabeledLattice.ordinaryDensity`, `OAI.LipschitzHilbert.SourceLabeledLattice.ordinaryTreeConstant` and `OAI.LipschitzHilbert.SourceLabeledLattice.physicalTreeSelectorValue` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proofs of `OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step` and `OAI.LipschitzHilbert.PacketLatticeData.exists_universal_ordinary_model_estimate` of this split import it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceOrdinaryTree.lean (declaration OAI.LipschitzHilbert.SourceLabeledLattice.exists_reference_ordinary_tree_estimate)

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
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem exists_reference_ordinary_tree_estimate (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B K : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (_hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (t a b w tau radius Lip eta sigma : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      0<w → P.topLength≤tau → 0≤Lip → 0≤eta → 0 ≤ sigma →
      1 ≤ radius+Cb → radius+Cb≤(2:ℝ)^K →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ q : P.PacketIndex, t∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ j l, t+P.rowSlope j l∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, ‖c j l v‖ ≤ sigma) →
      P.angularSeparatedTreeEnergy cb w c ≤ sigma^2*(P.topLength*P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k, selector j l k t≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 →
        |s-(t+P.rowSlope j l)| ≤ radius*(w/P.length j)) →
      (∀ j l k s, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q, P.ordinaryDensity t cell grid w tau E u q≤eta) →
      let F := fun z => P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u z)) z
      IntegrableOn F E (volume.prod volume) ∧
        (∫ z in E, ‖F z‖ ∂volume.prod volume)≤
          P.ordinaryTreeConstant C B K Lip*sigma*eta*P.topLength*P.width := by
  sorry

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end
