-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_actual_sharp_band_uniform_high
-- name    : OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:48:19.918233+00:00
-- url     : https://prove2.me/theorems/a466794a-7ea8-4f81-b3bd-d19cfd21024a
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high` of [lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandUniformHigh.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandUniformHigh.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem actual_sharp_band_uniform_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
--       (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
--       ∃ C L0 : ℝ, 0<C ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
--       ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
--       ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
--       ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
--         0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
--         (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
--         (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
--         (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
--       ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
--         ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
--           (schwartzVerticalProjection p w 0 f) g‖≤C*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.HorizontalHilbertInput`, `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` and `OAI.LipschitzHilbert.PacketRepresentation.sharpTimeKernel` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates` and `OAI.LipschitzHilbert.PacketRepresentation.schwartzVerticalProjection` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.kernelPairing` (definitions bundle `OAIQ090A002` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/SharpBandUniformHigh.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high)

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
open Set MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_uniform_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1 ≤ s ∧ s≤2) :
    ∃ C L0 : ℝ, 0<C ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ) (F E ratio : ℝ),
      0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r : ℝ, 600*(r-l)≤1 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
        (schwartzVerticalProjection p w 0 f) g‖≤C*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
