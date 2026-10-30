-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_actual_sharp_band_measurable_restricted_log
-- name    : OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:48:18.505783+00:00
-- url     : https://prove2.me/theorems/34acd796-301d-4ace-bb85-b22fafc51c50
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log` of [lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandMeasurableRestricted.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandMeasurableRestricted.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory Function`, `open scoped ENNReal`):
--
--   ```lean
--   theorem actual_sharp_band_measurable_restricted_log
--       (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput)
--       (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
--       ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
--       ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
--       ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
--         (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
--       ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
--         0<planeMeasure.real F → 0<planeMeasure.real E → support f⊆F → support g⊆E →
--       ∀ l r : ℝ, 1200*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
--       ∀ (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure),
--         ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w (hf2.toLp f) (hg2.toLp g)‖≤
--           restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.HorizontalHilbertInput`, `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput` and `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.PacketRepresentation.restrictedLogFactor` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.sharpBandL2Pairing` (definitions bundle `OAIQ090A002` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.conditional_variable_slope_truncation` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandMeasurableRestricted.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_measurable_restricted_log
    (hVariation : LepingleInput) (hLL : LaceyLiInput) (hH : HorizontalHilbertInput)
    (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ (f g : (ℝ×ℝ) → ℂ), Measurable f → Measurable g →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E → support f⊆F → support g⊆E →
    ∀ l r : ℝ, 1200*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
    ∀ (hf2 : MemLp f 2 planeMeasure) (hg2 : MemLp g 2 planeMeasure),
      ‖sharpBandL2Pairing epsilon R he (he.trans_le heR) field hfield p w (hf2.toLp f) (hg2.toLp g)‖≤
        restrictedLogFactor C (planeMeasure.real F) (planeMeasure.real E) := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
