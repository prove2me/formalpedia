-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_supported_selector_path_predictor
-- name    : OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:46:33.519998+00:00
-- url     : https://prove2.me/theorems/6fb3cbf7-b059-4707-a809-a075cb54fd91
-- title:
--   OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor` of [lean/OAI/Analysis/LipschitzHilbert/Phase/SourceSupportedSelectorPathPredictor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/SourceSupportedSelectorPathPredictor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.AngularGrid`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`, `open PhaseCombinatorics`):
--
--   ```lean
--   theorem eventually_source_supported_selector_path_predictor
--       (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
--       (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
--       (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (ι κ : Type) [Fintype κ]
--         (tops : Finset ι) (T : ι → SlopeBox)
--         (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
--         [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
--         (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
--         (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
--       ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
--         (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
--           (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
--         (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
--       ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
--       (∀ t j l k, Measurable (selector t j l k)) →
--       (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
--       ∀ (v : ℝ × ℝ → ℝ), Measurable v →
--       ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
--       ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
--         (g.branching:ℝ) = SourceParameters.step L →
--         (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
--         (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
--         (P t).length j ≤ (T t).length) →
--         (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
--           (w/(P t).length j) 0) →
--       ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
--       ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
--         (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
--           (w/(T t).length) (M t)) →
--         (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
--           (w/(T t).length) k → k ≤ M t) →
--       ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
--         0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
--         (∀ τ, τ ≠ σ → (phase τ).re = 0) →
--         (phase σ).re = phaseMu D (Real.sqrt L) →
--         0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
--       ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
--         (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
--         (∀ t ∈ tops, (P t).frequency = eta) →
--         (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
--         Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
--       let Q := fun t => (P t).withProfile (alt t) (hAlt t)
--       let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
--       let lower := ShiftedBlocks.endpoint σ j
--       let upper := ShiftedBlocks.endpoint σ (j+1)
--       let cut := g.rootWidth/(SourceParameters.branching L)^2
--       let slope := fun t => (T t).slope
--       let precision := fun t => w/(T t).length
--       let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
--       let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
--       let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
--         (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
--         (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
--         (fun p => (Q p.1).rawBand
--           (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
--           0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
--         (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
--       (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
--         |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
--         ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
--           ‖covariantSignal (P t).frequency
--             (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
--       ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
--       let cells := g.sourceBlockCells tops slope precision cut lower upper parent
--       let n := fun zz => g.mass tops slope precision cut weight lower parent zz
--       let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
--       let lam := fun zz (i : cells) => g.packetPathProduct
--         (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
--           (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
--         lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
--       let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
--         (sourceLineScale_pos g L hw upper)
--       ∀ (top : ι), top ∈ tops → g.index lower (slope top) = parent →
--         g.eligible cut (precision top) lower →
--         0 ≤ u → n z ≤ L^Cmass*Nmass →
--         pathDrop (g.shiftedPathMass tops slope precision cut weight σ top z) j ≤ u →
--         origin ≤ z.1 → z.1 ≤ origin+grid.width →
--         (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
--           (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
--           (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
--           (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
--           (I.card:ℝ) ≤ D/100) →
--         ∃ Γ : ℝ → ℝ, Measurable Γ ∧
--           Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
--           (∀ b, 0 ≤ Γ b) ∧
--           (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
--           (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
--           ∀ b ∈ grid.root,
--             sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
--               (n ((b,z.2+sR*(b-z.1)))) (c ((b,z.2+sR*(b-z.1))))
--               (fun i => wave ((b,z.2+sR*(b-z.1))) i.val) (lam ((b,z.2+sR*(b-z.1)))) ≤
--               Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLabeledLattice`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.sourceLineGrid`, `OAI.LipschitzHilbert.sourceLineScale`, `OAI.LipschitzHilbert.sourceLineScale_pos`, `OAI.LipschitzHilbert.sourcePredictionValue`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.index`, `OAI.LipschitzHilbert.AngularGrid.lastEligible`, `OAI.LipschitzHilbert.AngularGrid.mass`, `OAI.LipschitzHilbert.AngularGrid.packetPathProduct`, `OAI.LipschitzHilbert.AngularGrid.shiftedPathMass`, `OAI.LipschitzHilbert.AngularGrid.sourceBlockCells`, `OAI.LipschitzHilbert.AngularGrid.sourceBlockTop`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryGap`, `OAI.LipschitzHilbert.AngularGrid.sourceGap`, `OAI.LipschitzHilbert.AngularGrid.sourcePacketAmplitude`, `OAI.LipschitzHilbert.AngularGrid.sourceTransition`, `OAI.LipschitzHilbert.FiniteLineGrid.index`, `OAI.LipschitzHilbert.FiniteLineGrid.root`, `OAI.LipschitzHilbert.ShiftedBlocks.endpoint`, `OAI.LipschitzHilbert.SlopeBox.mask`, `OAI.LipschitzHilbert.SlopeBox.radius`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceLabeledLattice.constant`, `OAI.LipschitzHilbert.SourceLabeledLattice.length`, `OAI.LipschitzHilbert.SourceLabeledLattice.length_pos`, `OAI.LipschitzHilbert.SourceLabeledLattice.physicalMultiplierCoefficient`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawBand`, `OAI.LipschitzHilbert.SourceLabeledLattice.rawInterval`, `OAI.LipschitzHilbert.SourceLabeledLattice.withProfile`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.branching` and `OAI.LipschitzHilbert.SourceParameters.step` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.covariantSignal`, `OAI.LipschitzHilbert.intervalProbability`, `OAI.LipschitzHilbert.pathDrop`, `OAI.LipschitzHilbert.PhaseCombinatorics.phaseMu` and `OAI.LipschitzHilbert.ShiftedBlocks.tag` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.SourceSupportedLabeledTopGeometry` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_plane_integral` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/SourceSupportedSelectorPathPredictor.lean (declaration OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor)

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
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_path_predictor
    (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι κ : Type) [Fintype κ]
      (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
      (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
      (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
      (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(P t).length j) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
      (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (Q p.1).rawBand
        (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
        0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
      (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
    ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
    let cells := g.sourceBlockCells tops slope precision cut lower upper parent
    let n := fun zz => g.mass tops slope precision cut weight lower parent zz
    let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
    let lam := fun zz (i : cells) => g.packetPathProduct
      (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ (top : ι), top ∈ tops → g.index lower (slope top) = parent →
      g.eligible cut (precision top) lower →
      0 ≤ u → n z ≤ L^Cmass*Nmass →
      pathDrop (g.shiftedPathMass tops slope precision cut weight σ top z) j ≤ u →
      origin ≤ z.1 → z.1 ≤ origin+grid.width →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root,
          sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
            (n ((b,z.2+sR*(b-z.1)))) (c ((b,z.2+sR*(b-z.1))))
            (fun i => wave ((b,z.2+sR*(b-z.1))) i.val) (lam ((b,z.2+sR*(b-z.1)))) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  sorry

end LipschitzHilbert.AngularGrid

end

end OAI
end
