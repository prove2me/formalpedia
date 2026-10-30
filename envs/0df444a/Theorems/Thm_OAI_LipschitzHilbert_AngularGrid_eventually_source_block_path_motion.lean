-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_block_path_motion
-- name    : OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:35:38.285994+00:00
-- url     : https://prove2.me/theorems/664117d4-bd06-4c52-94f7-9c0fe7a8b07a
-- title:
--   OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceBlockPathMotion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceBlockPathMotion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.AngularGrid`, with `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--    theorem eventually_source_block_path_motion (D : ℝ) (hD : 0 ≤ D) :
--       ∀ᶠ L : ℝ in atTop,
--       ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
--         (w Kw : ℝ), 0 < w → 1 ≤ Kw →
--         (g.branching:ℝ) = SourceParameters.step L →
--         (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
--       ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
--         (j : ℕ), ((ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j:ℕ):ℝ) ≤ L^2 →
--       ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (Z μ p u : ℝ),
--         0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
--         (∀ τ, τ ≠ σ → (phase τ).re = 0) → (phase σ).re = μ →
--         0 ≤ μ → μ ≤ 1 → 1 ≤ p → 0 ≤ 1-μ-1/p → 0 ≤ u →
--       ∀ (top : ι), top ∈ tops →
--         g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
--           (ShiftedBlocks.endpoint σ (j+1)) →
--       ∀ (sR : ℝ), g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
--         g.index (ShiftedBlocks.endpoint σ j) sR →
--       ∀ (z : ℝ × ℝ),
--       let lower := ShiftedBlocks.endpoint σ j
--       let upper := ShiftedBlocks.endpoint σ (j+1)
--       let weight := fun t zz => (T t).weight Kw D zz
--       let n := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
--         (g.rootWidth/(SourceParameters.branching L)^2) weight lower (g.index lower (T top).slope) zz
--       let c := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
--         (g.rootWidth/(SourceParameters.branching L)^2) weight upper (g.index upper (T top).slope) zz
--       let lam := fun zz => g.packetPathProduct
--         (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
--           (g.rootWidth/(SourceParameters.branching L)^2) weight (SourceParameters.blockCount L)
--           (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
--         lower upper (T top).slope
--       let coeff := fun zz => (c zz/n zz)^(1-μ-1/p)*‖lam zz‖
--       1-c z/n z ≤ u →
--       ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ q ≤ SourceParameters.step L^(-(1/8:ℝ)) ∧
--         lam z ≠ 0 ∧ 0 ≤ coeff z ∧ coeff z ≤ 1 ∧ 1-coeff z ≤ 2*u ∧
--         ∀ b : ℝ, |b| ≤ sourceLineScale g L w upper →
--           ‖lam (SlopeBox.lineShift sR b z)-lam z‖ ≤ q*‖lam z‖ ∧
--           |coeff (SlopeBox.lineShift sR b z)-coeff z| ≤
--             24*SourceParameters.step L^(-(1/8:ℝ))*u
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.sourceLineScale`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.index`, `OAI.LipschitzHilbert.AngularGrid.mass`, `OAI.LipschitzHilbert.AngularGrid.packetPathProduct`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryGap`, `OAI.LipschitzHilbert.AngularGrid.sourceTransition`, `OAI.LipschitzHilbert.ShiftedBlocks.endpoint`, `OAI.LipschitzHilbert.SlopeBox.weight`, `OAI.LipschitzHilbert.SourceParameters.blockCount`, `OAI.LipschitzHilbert.SourceParameters.branching` and `OAI.LipschitzHilbert.SourceParameters.step` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.ShiftedBlocks.tag` and `OAI.LipschitzHilbert.SlopeBox.lineShift` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.AngularGrid.eventually_source_supported_selector_path_predictor` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceBlockPathMotion.lean (declaration OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid

 theorem eventually_source_block_path_motion (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hKb : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ), ((ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j:ℕ):ℝ) ≤ L^2 →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (Z μ p u : ℝ),
      0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) → (phase σ).re = μ →
      0 ≤ μ → μ ≤ 1 → 1 ≤ p → 0 ≤ 1-μ-1/p → 0 ≤ u →
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ (j+1)) →
    ∀ (sR : ℝ), g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR →
    ∀ (z : ℝ × ℝ),
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let weight := fun t zz => (T t).weight Kw D zz
    let n := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight lower (g.index lower (T top).slope) zz
    let c := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/(SourceParameters.branching L)^2) weight upper (g.index upper (T top).slope) zz
    let lam := fun zz => g.packetPathProduct
      (g.sourceTransition tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/(SourceParameters.branching L)^2) weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (T top).slope
    let coeff := fun zz => (c zz/n zz)^(1-μ-1/p)*‖lam zz‖
    1-c z/n z ≤ u →
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ q ≤ SourceParameters.step L^(-(1/8:ℝ)) ∧
      lam z ≠ 0 ∧ 0 ≤ coeff z ∧ coeff z ≤ 1 ∧ 1-coeff z ≤ 2*u ∧
      ∀ b : ℝ, |b| ≤ sourceLineScale g L w upper →
        ‖lam (SlopeBox.lineShift sR b z)-lam z‖ ≤ q*‖lam z‖ ∧
        |coeff (SlopeBox.lineShift sR b z)-coeff z| ≤
          24*SourceParameters.step L^(-(1/8:ℝ))*u := by
  sorry

end LipschitzHilbert.AngularGrid

end

end OAI
end
