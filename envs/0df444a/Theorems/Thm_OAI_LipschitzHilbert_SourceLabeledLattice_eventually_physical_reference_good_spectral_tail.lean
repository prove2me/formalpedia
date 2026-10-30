-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_eventually_physical_reference_good_spectral_tail
-- name    : OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:41:35.538416+00:00
-- url     : https://prove2.me/theorems/50b74b6d-9cdf-4ee8-8016-e0fe1d297786
-- title:
--   OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceLabeledSpectralGoodTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceLabeledSpectralGoodTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLabeledLattice`, with `open Filter MeasureTheory Set`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem eventually_physical_reference_good_spectral_tail (hVariation : LepingleInput)
--       (B : ℕ) (a q p J A F cStar cEta CEta cb Cb maskCone : ℝ)
--       (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
--       (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
--       (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order →
--         P.absoluteConstant ≤ L^a → P.absoluteConstant ≤ L^q →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
--         (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
--         (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (c : ℝ), 0 ≤ c →
--       ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ)
--         (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
--         (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
--         (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
--         (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
--         (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
--         (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
--           |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--         (∀ j l u k xi eta,
--           planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
--           |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--         (∀ j l, (∃ k, b j l k t ≠ 0) →
--           cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
--       ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
--         (∀ j l u, P.length j ≤ (T j l u).length) →
--         (∀ j l u, P.length j ≤ R → |P.rowSlope j l| ≤ Cb*w/P.length j →
--           |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
--       ∀ (y u H : ℝ), 0 < H → R ≤ H →
--         (volume.restrict (Ico u (u+H)))
--           {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
--           ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H →
--         (volume.restrict (Ico u (u+H)))
--           {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
--             (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
--           ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice.absoluteConstant`, `OAI.LipschitzHilbert.SourceLabeledLattice.frozenActiveLabels`, `OAI.LipschitzHilbert.SourceLabeledLattice.length`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalAngularError`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalPacket`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalReferenceBad` and `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.eventually_polynomial_uniform_selected_reference_good_path` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceLabeledSpectralGoodTail.lean (declaration OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_physical_reference_good_spectral_tail (hVariation : LepingleInput)
    (B : ℕ) (a q p J A F cStar cEta CEta cb Cb maskCone : ℝ)
    (hq : 0 ≤ q) (hJ : 0 ≤ J) (hA : 1 < A) (hF : 0 ≤ F) (hcStar : 0 ≤ cStar)
    (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hmaskCone : 0 ≤ maskCone) (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order →
      P.absoluteConstant ≤ L^a → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t R w : ℝ) (_hw : 0 < w) (_hwide : Cb*w ≤ P.width)
      (_hfrequency : ∀ k, |P.frequency k| ≤ F/w) (c : ℝ), 0 ≤ c →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (_hb : ∀ j l k, Measurable (b j l k)) (_hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
      (v : ℝ×ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1),
      (∀ j l k, b j l k t ≠ 0 → P.length j ≤ R) →
      (∀ j, (P.frozenActiveLabels t b j).card ≤ B) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l u k) (xi,eta) ≠ 0 →
        |xi+(t+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l, (∃ k, b j l k t ≠ 0) →
        cb*w/P.length j ≤ |P.rowSlope j l| ∧ |P.rowSlope j l| ≤ Cb*w/P.length j) →
    ∀ (T : ∀ j (l : P.labels j), Item j l → SlopeBox),
      (∀ j l u, P.length j ≤ (T j l u).length) →
      (∀ j l u, P.length j ≤ R → |P.rowSlope j l| ≤ Cb*w/P.length j →
        |t-(T j l u).slope| ≤ maskCone*(T j l u).width/P.length j) →
    ∀ (y u H : ℝ), 0 < H → R ≤ H →
      (volume.restrict (Ico u (u+H)))
        {x | L^(p+7) ≤ P.physicalAngularError t c b v g (x,y+t*x)} ≤
        ENNReal.ofReal (Real.exp (-(J+2)*L))*ENNReal.ofReal H →
      (volume.restrict (Ico u (u+H)))
        {x | (x,y+t*x) ∈ P.physicalReferenceBad alt hAlt t c b v g T L A
          (p+7) (2*q+9) (max (2*q+10) (a+p+7)+1)} ≤
        ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal H := by
  sorry

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end
