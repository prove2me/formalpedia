-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_ordinary_capped_removal_step
-- name    : OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:48:13.411488+00:00
-- url     : https://prove2.me/theorems/0978591c-d699-43b0-ae07-1bb46c50e3f9
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step` of [lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataCappedRemovalStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataCappedRemovalStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Set MeasureTheory`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem exists_ordinary_capped_removal_step (hL : LepingleInput)
--       (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
--       (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
--       (hspectral : cStar < cEta*cb) :
--       ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
--         (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item) (M Q gap packGap R K D0 : ℕ),
--       ∀ (w tau sigma D epsilon A margin F radius Lip eta density cap : ℝ),
--         0 < sigma → 0≤D → 0 ≤ cap → 0<epsilon → 0<eta → 0≤density → 0≤Lip →
--         0<w → w≤P.width → 0≤F → (∀ k, |P.frequency k|≤F/w) →
--         (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
--         (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
--         2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
--         (1:ℝ)≤R → 207≤P.order → A≤D0 → tau≤P.topLength →
--         1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
--       ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
--         (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
--       ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ), c=P.ordinaryCoefficient g →
--       ∀ (initial : Finset P.PacketIndex),
--         (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
--           P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
--         (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
--           P.unsignedSizeTestEnergy w cb cell grid c initial T ≤ cap^2*T.area) →
--         (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
--           grid q.1.val (cell q.1 q.2.1)) →
--         (∀ q∈initial, epsilon ≤ cb*(w/P.length q.1)/4) →
--         (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
--           |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
--         (∀ s∈initial, ∀ k xi et,
--           planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
--           Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
--             scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
--         (∀ q∈initial, ∀ k xi et,
--           planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
--           |et-P.frequency k|≤Cv/P.width) →
--       ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
--         (∀ j l k, Measurable (selector j l k)) →
--         (∀ j l k s, ‖selector j l k s‖≤1) →
--         (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
--         (∀ j l k s, selector j l k s≠0 →
--           s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
--         (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
--         (∀ j l k s t, |s-t|≤w/P.length j →
--           ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
--       ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
--       ∀ (u : ℝ×ℝ → ℝ), Measurable u →
--         (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
--       ∃ remaining : Finset P.PacketIndex, remaining⊆initial ∧
--         (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
--         (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
--           P.unsignedSizeTestEnergy w cb cell grid c remaining T ≤ sigma^2*T.area) ∧
--         let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
--           selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
--         IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
--         (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
--           (625*densityRadiusConstant^2)*P.referenceTreeConstant CD ((2*R+1)*M) K Lip*
--             cap*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) +
--           (((4*D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*R+1)*M) K Lip*cap*density*
--             ((4*(selectedNearConstant P gap M Q+
--               2*Real.sqrt (2*selectedFarConstant P cb D CS packGap M Q))/sigma^2)*
--                 ∫ z, ‖g z‖^2 ∂volume.prod volume)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.densityRadiusConstant`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.scaledAngularCell`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.ordinaryCoefficient`, `OAI.LipschitzHilbert.PacketLatticeData.ordinaryDensity`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.referenceTreeConstant`, `OAI.LipschitzHilbert.PacketLatticeData.selectedFarConstant`, `OAI.LipschitzHilbert.PacketLatticeData.selectedNearConstant`, `OAI.LipschitzHilbert.SlopeBox.area` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.PacketLatticeData.unsignedSizeTestEnergy` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/PacketDataCappedRemovalStep.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.exists_ordinary_capped_removal_step)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section

attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_ordinary_capped_removal_step (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q gap packGap R K D0 : ℕ),
    ∀ (w tau sigma D epsilon A margin F radius Lip eta density cap : ℝ),
      0 < sigma → 0≤D → 0 ≤ cap → 0<epsilon → 0<eta → 0≤density → 0≤Lip →
      0<w → w≤P.width → 0≤F → (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4 →
      (1+cb/4)/(2:ℝ)^packGap ≤ cb/4 → cb/2 ≤ margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (1:ℝ)≤R → 207≤P.order → A≤D0 → tau≤P.topLength →
      1 ≤ radius+1 → radius+1≤(2:ℝ)^K →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ), c=P.ordinaryCoefficient g →
    ∀ (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T ≤ cap^2*T.area) →
      (∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
        grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon ≤ cb*(w/P.length q.1)/4) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ s∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
      (∀ q∈initial, ∀ k xi et,
        planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (selector j l k)) →
      (∀ j l k s, ‖selector j l k s‖≤1) →
      (∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, selector j l k s≠0 →
        s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) →
      (∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j →
        ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      (∀ q∈initial, P.ordinaryDensity 0 cell grid w tau E u q≤density) →
    ∃ remaining : Finset P.PacketIndex, remaining⊆initial ∧
      (∀ q∈remaining, P.ordinaryDensity 0 cell grid w tau E u q≤eta) ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T ≤ sigma^2*T.area) ∧
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      IntegrableOn (fun z => (∑ q∈initial, V q z)-(∑ q∈remaining, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈initial, V q z)-(∑ q∈remaining, V q z)‖ ∂volume.prod volume)≤
        (625*densityRadiusConstant^2)*P.referenceTreeConstant CD ((2*R+1)*M) K Lip*
          cap*density*(1+eta^(-(1/20:ℝ)))*(2*(volume.prod volume).real E/eta) +
        (((4*D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*R+1)*M) K Lip*cap*density*
          ((4*(selectedNearConstant P gap M Q+
            2*Real.sqrt (2*selectedFarConstant P cb D CS packGap M Q))/sigma^2)*
              ∫ z, ‖g z‖^2 ∂volume.prod volume) := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
