-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_supported_transverse_tree_maximal
-- name    : OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:51:26.493347+00:00
-- url     : https://prove2.me/theorems/d0c247aa-5853-40c4-86b4-2fc057889246
-- title:
--   OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal` of [lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedTreeMaximal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedTreeMaximal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLabeledLattice`, with `open MeasureTheory`, `open scoped BigOperators FourierTransform`):
--
--   ```lean
--   theorem exists_supported_transverse_tree_maximal (hL : LepingleInput)
--       (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
--       ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
--         (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
--       ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
--         (∀ j l v, |P.actualZ j l v-b|≤P.width) →
--         (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
--           |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
--         (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l| ∧
--           |P.rowSlope j l|≤Cb*w/P.length j) →
--         let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
--           P.physicalTreeMaximal t c z^2
--         Integrable E (volume.prod volume) ∧
--         (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2*
--           ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.SourceLabeledLattice.absoluteConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice.actualZ`, `OAI.LipschitzHilbert.SourceLabeledLattice.length` and `OAI.LipschitzHilbert.SourceLabeledLattice.physicalPacket` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.polynomialWeight` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.SourceLabeledLattice.physicalTreeMaximal` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedTreeMaximal.lean (declaration OAI.LipschitzHilbert.SourceLabeledLattice.exists_supported_transverse_tree_maximal)

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
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem exists_supported_transverse_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l v, |P.actualZ j l v-b|≤P.width) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2*
        ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
  sorry

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end
