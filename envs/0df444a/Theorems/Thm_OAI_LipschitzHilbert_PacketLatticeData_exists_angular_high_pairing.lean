-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_angular_high_pairing
-- name    : OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:38:46.638442+00:00
-- url     : https://prove2.me/theorems/04844d67-4164-4d1c-8808-7e565a240bdc
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing` of [lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularHighPairing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularHighPairing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Set MeasureTheory`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem exists_angular_high_pairing (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (cStar cEta CEta cb Cv radius F c0 cone p0 decay : ℝ) (D K H J : ℕ)
--       (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
--       (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4)
--       (hr : 0 ≤ radius) (hF : 0≤F) (hc0 : 0 < c0) (hcone : 1 ≤ cone)
--       (hrcone : radius ≤ cone) (hconeK : cone≤K) (hp0 : 0≤p0) (hdecay : 0≤decay)
--       (hD : 4≤D) (hJ : 2*cone+1≤(2:ℝ)^J)
--       (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
--       (num : OrdinaryModelNumerics cStar cEta cb radius) :
--       ∃ A L0 : ℝ, 0≤A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex) (w : ℝ),
--         0<w → w≤P.width → 207≤P.order → 6+2*(8*D+1)≤P.order →
--         P.scale=4*(L^(A+2)*P.width) → P.ratioBound=4*L^(A+2) →
--         (2^P.order*P.profileBound)*3^(2*P.order)≤L^p0 →
--         P.topLength≤Real.exp (-(L^(97/100:ℝ))) →
--         (∀ k, c0/w≤|P.frequency k|) → (∀ k, |P.frequency k|≤F/w) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) H) →
--         (∀ j l, |P.rowSlope j l|+w/P.length j≤1) →
--         (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
--           |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
--         (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
--           |et-P.frequency k|≤Cv/P.width) →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
--         (∀ j l a k xi et,
--           planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
--           |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
--         (∀ j l a k xi et,
--           planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
--           |et-P.frequency k|≤Cv/P.width) →
--       ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
--         (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
--         (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
--         (∀ j l k s t, ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
--       ∀ (field : Plane → ℝ), LipschitzWith 1 field →
--       ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
--         (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
--       ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
--         (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
--         0<(volume.prod volume).real Fset →
--         (∀ z, z∉E → f z=0) → (∀ z, z∉Fset → g z=0) →
--       ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
--         (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
--         0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
--         (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
--         Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
--         P.width=widthScale*w →
--         Integrable (fun z => inner ℂ
--           (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z))
--           (volume.prod volume) ∧
--         ‖∫ z, inner ℂ
--           (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z)
--           ∂volume.prod volume‖≤6*L^(-decay)*ratio*(volume.prod volume).real Fset
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.PacketLatticeData.OrdinaryModelNumerics`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.crossPacketValue`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.withProfile` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.exists_finite_diagonal_high_l1` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularHighPairing.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_high_pairing (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cv radius F c0 cone p0 decay : ℝ) (D K H J : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4)
    (hr : 0 ≤ radius) (hF : 0≤F) (hc0 : 0 < c0) (hcone : 1 ≤ cone)
    (hrcone : radius ≤ cone) (hconeK : cone≤K) (hp0 : 0≤p0) (hdecay : 0≤decay)
    (hD : 4≤D) (hJ : 2*cone+1≤(2:ℝ)^J)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ A L0 : ℝ, 0≤A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex) (w : ℝ),
      0<w → w≤P.width → 207≤P.order → 6+2*(8*D+1)≤P.order →
      P.scale=4*(L^(A+2)*P.width) → P.ratioBound=4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order)≤L^p0 →
      P.topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ k, c0/w≤|P.frequency k|) → (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) H) →
      (∀ j l, |P.rowSlope j l|+w/P.length j≤1) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field →
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      0<(volume.prod volume).real Fset →
      (∀ z, z∉E → f z=0) → (∀ z, z∉Fset → g z=0) →
    ∀ l r ratio widthScale : ℝ, 600*(r-l)≤1 →
      (∀ z∈E, z.1∈Icc l r) → (∀ z∈Fset, z.1∈Icc l r) →
      0 < ratio → L/2≤Real.log ratio → Real.log ratio≤2*L →
      (volume.prod volume).real E=ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ))≤widthScale → widthScale≤2*Real.exp (L^(9/10:ℝ)) →
      P.width=widthScale*w →
      Integrable (fun z => inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ
        (∑ a∈S, P.crossPacketValue alt hAlt 0 b (fun z => field (planeCoordinates z)) f z a) (g z)
        ∂volume.prod volume‖≤6*L^(-decay)*ratio*(volume.prod volume).real Fset := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
