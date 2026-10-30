-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_angular_reverse_pairing
-- name    : OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:38:45.769095+00:00
-- url     : https://prove2.me/theorems/aefdf165-60f4-4dcf-8600-9450132d086d
-- title:
--   OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing` of [lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularReversePairing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularReversePairing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketLatticeData`, with `open Set MeasureTheory`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem exists_angular_reverse_pairing (hVariation : LepingleInput)
--       (cStar cEta CEta cb Cv radius : ℝ) (M : ℕ)
--       (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
--       (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4) (hr : 0 ≤ radius)
--       (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
--       (num : OrdinaryModelNumerics cStar cEta cb radius) :
--       ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex),
--       ∀ w F : ℝ, 0<w → w≤P.width → 0≤F → 207≤P.order →
--         (∀ k, |P.frequency k|≤F/w) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
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
--         (∀ j l k s t, |s-t|≤w/P.length j → ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
--       ∀ bound : ℝ, 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
--       ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
--         (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
--       ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
--         (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
--         (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
--       ∀ u : ℝ×ℝ → ℝ, Measurable u →
--         Integrable (fun z => inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z))
--           (volume.prod volume) ∧
--         ‖∫ z, inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z)
--           ∂volume.prod volume‖≤3*((num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
--             Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
--             ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketLatticeData`, `OAI.LipschitzHilbert.planarAngularFourier`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.PacketLatticeData.OrdinaryModelNumerics`, `OAI.LipschitzHilbert.PacketLatticeData.PacketIndex`, `OAI.LipschitzHilbert.PacketLatticeData.crossPacketValue`, `OAI.LipschitzHilbert.PacketLatticeData.length`, `OAI.LipschitzHilbert.PacketLatticeData.physicalPacket`, `OAI.LipschitzHilbert.PacketLatticeData.withProfile`, `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` and `OAI.LipschitzHilbert.PacketLatticeData.OrdinaryModelNumerics.reverseUnitCost` (definitions bundle `OAIQ090A000` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/PacketAngularReversePairing.lean (declaration OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing)

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
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_reverse_pairing (hVariation : LepingleInput)
    (cStar cEta CEta cb Cv radius : ℝ) (M : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4) (hr : 0 ≤ radius)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex),
    ∀ w F : ℝ, 0<w → w≤P.width → 0≤F → 207≤P.order →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
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
      (∀ j l k s t, |s-t|≤w/P.length j → ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ bound : ℝ, 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    ∀ u : ℝ×ℝ → ℝ, Measurable u →
      Integrable (fun z => inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z)
        ∂volume.prod volume‖≤3*((num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by
  sorry

end LipschitzHilbert.PacketLatticeData

end

end OAI
end
