-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_source_density_popular_recovery
-- name    : OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:42:09.728787+00:00
-- url     : https://prove2.me/theorems/bea9293d-5094-4152-8802-36363b353943
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery` of [lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataDensityPopularRecovery.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataDensityPopularRecovery.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Set MeasureTheory Filter`, `open scoped BigOperators ENNReal NNReal Topology`):
--
--   ```lean
--   theorem source_density_popular_recovery
--       (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
--       (D K H J₀ : ℕ)
--       (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
--       (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
--       (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
--       (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
--       (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
--       (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
--       ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
--       ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item)
--         (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ), 0 < w →
--         P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
--         (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
--         6+2*(8*D+1) ≤ P.order →
--       ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
--         (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
--           (fun z => field (planeCoordinates z))),
--         let T := forest.top
--         (∀ i, |(T i).slope| ≤ 1) →
--       ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
--         (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
--         MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
--         0 < (volume.prod volume).real Fset →
--       ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
--         (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
--         Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
--         P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
--         (b : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
--         (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
--         (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
--         (∀ j l k s, b j l k s ≠ 0 →
--           cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
--             |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--           (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
--         (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
--         (∀ j l u k xi eta,
--           planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
--             |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--         (∀ j l u k xi eta,
--           planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
--             |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--       ∀ (v : ℝ×ℝ → ℝ), Measurable v →
--       ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
--       ∀ (g : AngularGrid) (start : ℝ), (g.branching:ℝ) = SourceParameters.step L →
--         (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
--         (∀ i, start ≤ (T i).slope ∧ (T i).slope ≤ start+g.rootWidth) →
--         (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
--           ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
--         (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
--           ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.PacketLatticeData.PacketDensityForest`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.crossPacketValue`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.withProfile`, `OAI.LipschitzHilbert.SourceParameters.branching`, `OAI.LipschitzHilbert.SourceParameters.step` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataDensityPopularRecovery.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery)

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
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_popular_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      (∀ i, |(T i).slope| ≤ 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (g : AngularGrid) (start : ℝ), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ i, start ≤ (T i).slope ∧ (T i).slope ≤ start+g.rootWidth) →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
