-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_source_supported_selector_amplitude_motion
-- name    : OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:46:41.398142+00:00
-- url     : https://prove2.me/theorems/a31a6000-4f9a-4df8-b237-65e6380aeb77
-- title:
--   OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion` of [lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedSelectorMotion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedSelectorMotion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.AngularGrid`, with `open MeasureTheory Filter`, `open scoped BigOperators`, `open PhaseCombinatorics`):
--
--   ```lean
--   theorem source_supported_selector_amplitude_motion (p : ℝ) (D Bslots : ℕ) :
--       ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
--       ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
--         (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [Fintype κ] [∀ j l, Fintype (Item j l)]
--         (P : ι → SourceLabeledLattice N κ Label Item),
--       (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
--       (∀ t ∈ tops, (P t).constant ≤ L^p) →
--       ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
--         (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
--           (P t).profileBound)
--         (Kw : ℝ), 1 ≤ Kw →
--       (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
--       ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
--       (∀ t j l k, Measurable (selector t j l k)) →
--       (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
--       ∀ (v : ℝ × ℝ → ℝ), Measurable v →
--       ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
--       ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
--       (∀ t ∈ tops, B^2*w ≤ (T t).width) →
--       (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
--         (P t).length j ≤ (T t).length) →
--       (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
--       ∀ (Kb : ℕ), 0 < Kb → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
--       ∀ (M : ι → ℕ),
--       (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
--       (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
--       (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
--       ∀ (sR : ℝ) (cell : ℤ),
--       (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
--         (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
--       g.width h ≤ B*g.width start →
--       ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
--       ∀ (z : ℝ × ℝ) (frequency : κ → ℝ) (Cfreq : ℝ), 0 ≤ Cfreq →
--       (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
--       ∀ (phase : ℕ → ℂ) (a Z C A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z →
--       (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
--       (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
--       1 ≤ C → (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A →
--       let Q := fun t => (P t).withProfile (alt t) (hAlt t)
--       let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
--       let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
--         (div_pos hw ((P t).length_pos j))
--       let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
--       (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
--         |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
--         ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
--           ‖covariantSignal (P t).frequency
--             (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
--           A*(weight t z)^8) →
--       let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
--         (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
--       let δ := (5*(D:ℝ)/Kw)/Real.sqrt (g.branching:ℝ)
--       let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
--       let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
--       let value := fun zz t j => (Q t).rawBand
--         (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
--         zz.1 (zz.2-(T t).slope*zz.1)
--       ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
--           (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
--           Prod.fst (fun p => stop p.1 p.2) (fun p => value (SlopeBox.lineShift sR b z) p.1 p.2)
--           phase a (SlopeBox.lineShift sR b z) start cell-
--         diagonalModulationIsometry frequency ((sR-g.center start cell)*b)
--           (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
--             (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
--             Prod.fst (fun p => stop p.1 p.2) (fun p => value z p.1 p.2)
--             phase a z start cell)‖ ≤
--         (V*((1+d)*(J/Real.sqrt (g.branching:ℝ))+d*A)*C^3)*
--           g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
--             (g.rootWidth/B^2) weight start cell z
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.AngularGrid.cellTops`, `OAI.LipschitzHilbert.AngularGrid.center`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.index`, `OAI.LipschitzHilbert.AngularGrid.lastEligible`, `OAI.LipschitzHilbert.AngularGrid.mass`, `OAI.LipschitzHilbert.AngularGrid.sourcePacketAmplitude`, `OAI.LipschitzHilbert.AngularGrid.width`, `OAI.LipschitzHilbert.SlopeBox.mask`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.constant`, `OAI.LipschitzHilbert.SourceLabeledLattice.length`, `OAI.LipschitzHilbert.SourceLabeledLattice.length_pos`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalMultiplierCoefficient`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawBand`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawInterval` and `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.covariantSignal`, `OAI.LipschitzHilbert.diagonalModulationIsometry` and `OAI.LipschitzHilbert.SlopeBox.lineShift` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.SourceSupportedLabeledTopGeometry` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.AngularGrid.source_supported_selector_normalized_motion` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Packets/SourceSupportedSelectorMotion.lean (declaration OAI.LipschitzHilbert.AngularGrid.source_supported_selector_amplitude_motion)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem source_supported_selector_amplitude_motion (p : ℝ) (D Bslots : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item),
    (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
    (∀ t ∈ tops, (P t).constant ≤ L^p) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (Kw : ℝ), 1 ≤ Kw →
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ) (Cfreq : ℝ), 0 ≤ Cfreq →
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z C A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    1 ≤ C → (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j))
    let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
        A*(weight t z)^8) →
    let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
      (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
    let δ := (5*(D:ℝ)/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
    let value := fun zz t j => (Q t).rawBand
      (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
      zz.1 (zz.2-(T t).slope*zz.1)
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2) (fun p => value (SlopeBox.lineShift sR b z) p.1 p.2)
        phase a (SlopeBox.lineShift sR b z) start cell-
      diagonalModulationIsometry frequency ((sR-g.center start cell)*b)
        (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
          Prod.fst (fun p => stop p.1 p.2) (fun p => value z p.1 p.2)
          phase a z start cell)‖ ≤
      (V*((1+d)*(J/Real.sqrt (g.branching:ℝ))+d*A)*C^3)*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight start cell z := by
  sorry

end LipschitzHilbert.AngularGrid

end

end OAI
end
