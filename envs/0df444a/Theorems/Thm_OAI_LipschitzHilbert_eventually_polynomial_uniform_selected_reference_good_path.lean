-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_eventually_polynomial_uniform_selected_reference_good_path
-- name    : OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:52:22.876862+00:00
-- url     : https://prove2.me/theorems/ec1ed85f-05b2-4b93-be2a-587bfff7a61e
-- title:
--   OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourcePolynomialSelectedGoodPath.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourcePolynomialSelectedGoodPath.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert`, with `open Filter MeasureTheory Set`, `open scoped Topology ENNReal BigOperators`):
--
--   ```lean
--   theorem eventually_polynomial_uniform_selected_reference_good_path
--       (hVariation : LepingleInput)
--       (D eventPower weightPower q A F cStar cEta CEta cb Cb maskCone Lip : ℝ)
--       (K Hlabels J₀ : ℕ) (hD : 2 < D)
--       (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
--       (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
--       (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
--       ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
--       ∀ (ι σ : Type*) (tops : Finset ι) (pathTop : ι → SlopeBox)
--         (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : ι → σ → PhysicalReferenceData N κ Label Item)
--         (Q : ∀ t i, Finset (P t i).family.PacketIndex) (base : Set (ℝ×ℝ)),
--         MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
--         (∀ t ∈ tops, ∀ i ∈ events t,
--           let R := P t i
--           6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = (pathTop t).slope ∧
--           ∃ (c Cwide radius : ℝ) (E Jcut : ℕ) (w : ℝ),
--             0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide ≤ c*(2:ℝ)^Jcut ∧
--             1 ≤ Cwide*((2:ℝ)^E)^4 ∧ radius ≤ K ∧
--             (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--               (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
--               (R.angle*(2:ℝ)^j.val) Hlabels) ∧
--             (∀ j l k, Measurable (R.selector j l k)) ∧
--             (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
--             (∀ j l k s, R.selector j l k s ≠ 0 →
--               |s-(R.slope+R.family.rowSlope j l)| ≤ radius*(R.angle*(2:ℝ)^j.val)) ∧
--             (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
--               ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
--                 Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
--             (∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
--               R.selector j l k s = 0) ∧
--             Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
--             Jcut ≤ J₀ ∧ E = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
--             0 < w ∧ Cb*w ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w) ∧
--             (∀ j l u k xi eta,
--               planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
--                 |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
--                   cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
--             (∀ j l u k xi eta,
--               planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
--                 R.slope j l u k) (xi,eta) ≠ 0 →
--                 |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
--                   cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
--             (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
--               cb*w/R.family.length j ≤ |R.family.rowSlope j l| ∧
--                 |R.family.rowSlope j l| ≤ Cb*w/R.family.length j) ∧
--             (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
--               R.family.length j ≤ (R.packetTop j l u).length) ∧
--             (∀ j (_l : R.family.labels j), R.family.length j ≤ (pathTop t).length) ∧
--             (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
--               R.family.length j ≤ (pathTop t).length →
--               |R.family.rowSlope j l| ≤ Cb*w/R.family.length j →
--               |R.slope-(R.packetTop j l u).slope| ≤
--                 maskCone*(R.packetTop j l u).width/R.family.length j)) →
--         let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad
--           L A (q+8) (2*q+9) (2*q+11)
--         let good := sourceGoodPathSet base tops (fun t => (pathTop t).weight Kw D) bad L
--         Integrable (sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad)
--           (volume.prod volume) ∧
--         (∫ z, sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad z
--           ∂volume.prod volume) ≤
--           (∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-10*L) ∧
--         MeasurableSet good ∧ good ⊆ base ∧
--         (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
--           ((∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-9*L)) ∧
--         ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
--           z ∉ ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) ∧
--           ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
--             finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
--               (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
--               (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
--               (2*H) ≤ (L^(2*q+11))^3
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PhysicalReferenceData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.finiteCubicVariation`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.PhysicalReferenceData.bad`, `OAI.LipschitzHilbert.PhysicalReferenceData.restrictPackets`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.PacketIndex`, `OAI.LipschitzHilbert.SourceLabeledLattice.RestrictedPacketItem`, `OAI.LipschitzHilbert.SourceLabeledLattice.absoluteConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.SourceLabeledLattice.length`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalPacket`, `OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype`, `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.stepExponent` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.sourceBadPathMass` and `OAI.LipschitzHilbert.sourceGoodPathSet` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.SourceLabeledLattice.selectedPhysicalPrefix` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourcePolynomialSelectedGoodPath.lean (declaration OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path)

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
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_polynomial_uniform_selected_reference_good_path
    (hVariation : LepingleInput)
    (D eventPower weightPower q A F cStar cEta CEta cb Cb maskCone Lip : ℝ)
    (K Hlabels J₀ : ℕ) (hD : 2 < D)
    (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hLip : 0 ≤ Lip) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (pathTop : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ i ∈ events t,
        let R := P t i
        6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = (pathTop t).slope ∧
        ∃ (c Cwide radius : ℝ) (E Jcut : ℕ) (w : ℝ),
          0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide ≤ c*(2:ℝ)^Jcut ∧
          1 ≤ Cwide*((2:ℝ)^E)^4 ∧ radius ≤ K ∧
          (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
            (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
            (R.angle*(2:ℝ)^j.val) Hlabels) ∧
          (∀ j l k, Measurable (R.selector j l k)) ∧
          (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
          (∀ j l k s, R.selector j l k s ≠ 0 →
            |s-(R.slope+R.family.rowSlope j l)| ≤ radius*(R.angle*(2:ℝ)^j.val)) ∧
          (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
            ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
              Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
          (∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
            R.selector j l k s = 0) ∧
          Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
          Jcut ≤ J₀ ∧ E = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
          0 < w ∧ Cb*w ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w) ∧
          (∀ j l u k xi eta,
            planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l u k xi eta,
            planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
              R.slope j l u k) (xi,eta) ≠ 0 →
              |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
                cEta ≤ w*eta ∧ w*eta ≤ CEta) ∧
          (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
            cb*w/R.family.length j ≤ |R.family.rowSlope j l| ∧
              |R.family.rowSlope j l| ≤ Cb*w/R.family.length j) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (R.packetTop j l u).length) ∧
          (∀ j (_l : R.family.labels j), R.family.length j ≤ (pathTop t).length) ∧
          (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ Q t i →
            R.family.length j ≤ (pathTop t).length →
            |R.family.rowSlope j l| ≤ Cb*w/R.family.length j →
            |R.slope-(R.packetTop j l u).slope| ≤
              maskCone*(R.packetTop j l u).width/R.family.length j)) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad
        L A (q+8) (2*q+9) (2*q+11)
      let good := sourceGoodPathSet base tops (fun t => (pathTop t).weight Kw D) bad L
      Integrable (sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad)
        (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops (fun t => (pathTop t).weight Kw D) bad z
        ∂volume.prod volume) ≤
        (∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (pathTop t).length*(pathTop t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
        z ∉ ((P t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11) ∧
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^(2*q+11))^3 := by
  sorry

end LipschitzHilbert

end

end OAI
end
