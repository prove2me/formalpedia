-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_scalar_band_reverse
-- name    : OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:50:37.139229+00:00
-- url     : https://prove2.me/theorems/ccd49f00-df43-4b55-b89b-ab6175d47bac
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse` of [lean/OAI/Analysis/LipschitzHilbert/Phase/ScalarBandDiagonal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/ScalarBandDiagonal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory`, `open scoped ENNReal BigOperators`):
--
--   ```lean
--   theorem scalar_band_reverse (hVariation : LepingleInput)
--       (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
--       (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
--       (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
--       (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
--       ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
--         0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
--       ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
--       ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
--         (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
--       ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
--         (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
--         ‖scalarBandForm psi beta N topLength W center u f g‖≤
--           K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
--             (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput` and `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.PacketRepresentation.scalarBandForm` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Phase/ScalarBandDiagonal.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.scalar_band_reverse)

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
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem scalar_band_reverse (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖scalarBandForm psi beta N topLength W center u f g‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
