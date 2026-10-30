-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_top_selector_concentration_of_supported
-- name    : OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:38:13.706997+00:00
-- url     : https://prove2.me/theorems/7f6483e7-e09e-4614-8e4c-a612f843ca8c
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported` of [lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataSupportedAssignedConcentration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataSupportedAssignedConcentration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`):
--
--   ```lean
--   theorem eventually_assigned_top_selector_concentration_of_supported (hL : LepingleInput)
--       (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
--       (hgap : cStar < cEta*cb)
--       (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
--       (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
--         (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
--         (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
--         P.referenceEnvelopeConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
--       ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j l u k,
--           planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
--         (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
--         (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
--         (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
--         (∀ top, P.width ≤ L^aWeight*(T top).width) →
--         (∀ top, P.scale = 4*(L^aWeight*(T top).width)) →
--         (∀ q ∈ packets,
--           |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
--             L^aWeight*(T (assigned q)).length) →
--         (∀ q ∈ packets,
--           |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
--             P.actualX q.1 q.2.1 q.2.2-
--             ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
--               L^aWeight*(T (assigned q)).width) →
--       ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
--         (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
--         wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
--         (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
--           (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
--       ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (b j l k)) →
--         (∀ j l k s, ‖b j l k s‖ ≤ 1) →
--         (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
--           b j l k s ≠ 0 →
--           |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
--         (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
--           |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
--           ‖b j l k s-b j l k (T top).slope‖ ≤
--             Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
--         (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
--           (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
--           b j l k s = 0) →
--       ∀ (v : ℝ×ℝ → ℝ), Measurable v →
--       ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
--         (∀ z, ‖f z‖ ≤ 1) →
--         (∀ q ∈ packets, ∀ k xi eta,
--           planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
--           |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
--             cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--         (∀ q ∈ packets, ∀ k xi eta,
--           planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
--             oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
--           |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
--             cEta ≤ w*eta ∧ w*eta ≤ CEta) →
--         (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
--           (∃ k, b j l k (T top).slope ≠ 0) →
--           cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
--             |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
--         J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
--         let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
--           oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
--         let orig := fun top j (l : (Q top).labels j) =>
--           ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
--             oldSlope (T top).slope (R top) cone w j l).val.2
--         let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
--           alt j (orig top j l) u.val k
--         let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
--           hAlt j (orig top j l) u.val k
--         ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
--           (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
--           ∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z shift,
--             |shift| ≤ (T top).width → z ∉ bad →
--             let V := fun x y => ((Q top).withProfile (a top) (ha top)).rawInterval
--               (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
--                 j (orig top j l) u.val) 0 lower upper x y
--             ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
--               ‖covariantSignal P.frequency (fun k y => V z.1 y k)
--                 (z.2-(T top).slope*z.1+shift)‖ ≤
--                   L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.PacketLatticeData.AssignedTopItem`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.actualX`, `OAI.LipschitzHilbert.PacketLatticeData.actualZ`, `OAI.LipschitzHilbert.PacketLatticeData.assignedTopFamily`, `OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.physicalMultiplierCoefficient`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.referenceCondition`, `OAI.LipschitzHilbert.PacketLatticeData.referenceEnvelopeConstant`, `OAI.LipschitzHilbert.PacketLatticeData.referenceFamily`, `OAI.LipschitzHilbert.PacketLatticeData.referenceOriginalLabel`, `OAI.LipschitzHilbert.PacketLatticeData.withProfile`, `OAI.LipschitzHilbert.SlopeBox.area`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawInterval`, `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.stepExponent` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.covariantSignal` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataSupportedAssignedConcentration.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_top_selector_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      P.referenceEnvelopeConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, P.scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let V := fun x y => ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
              j (orig top j l) u.val) 0 lower upper x y
          ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
            ‖covariantSignal P.frequency (fun k y => V z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
