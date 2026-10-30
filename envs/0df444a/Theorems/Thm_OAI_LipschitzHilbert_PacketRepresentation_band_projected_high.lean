-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_band_projected_high
-- name    : OAI.LipschitzHilbert.PacketRepresentation.band_projected_high
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:50:10.06382+00:00
-- url     : https://prove2.me/theorems/6e461d83-bbee-40be-96bd-bee0ee7ce060
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.band_projected_high: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.band_projected_high` of [lean/OAI/Analysis/LipschitzHilbert/Fourier/BandProjectedHigh.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/BandProjectedHigh.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory`, `open scoped ENNReal BigOperators`):
--
--   ```lean
--   theorem band_projected_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
--       (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
--       (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
--       (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
--       ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
--       ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
--         5*(w/W) ≤ c/2 → c/2≤C →
--         topLength≤Real.exp (-(L^(97/100:ℝ))) →
--         (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
--       ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
--       ∀ (f g : ℝ×ℝ → ℂ), Measurable f → Measurable g →
--         MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
--         Integrable f planeMeasure → Integrable g planeMeasure →
--       ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
--         (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
--         (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
--         (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
--       ∀ l r m : ℝ, 600*(r-l)≤1 →
--         (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
--         Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
--         let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
--         ‖finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
--           (fun n : I => verticalBinCenter ⌈C*W/w⌉₊ W n)
--           (fun z => field (planeCoordinates z))
--           (fun n z => verticalConvolution
--             (verticalProfileKernel verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)) f z)
--           (verticalBinVector I ⌈C*W/w⌉₊ W g)‖≤
--           A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LaceyLiInput`, `OAI.LipschitzHilbert.LepingleInput` and `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates`, `OAI.LipschitzHilbert.PacketRepresentation.verticalBinCenter`, `OAI.LipschitzHilbert.PacketRepresentation.verticalBinLabels`, `OAI.LipschitzHilbert.PacketRepresentation.verticalBinPlateau`, `OAI.LipschitzHilbert.PacketRepresentation.verticalBinProfile`, `OAI.LipschitzHilbert.PacketRepresentation.verticalBinVector`, `OAI.LipschitzHilbert.PacketRepresentation.verticalConvolution` and `OAI.LipschitzHilbert.PacketRepresentation.verticalProfileKernel` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.finiteDiagonalBandL1` (definitions bundle `OAIQ090A002` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_uniform_high` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/BandProjectedHigh.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.band_projected_high)

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
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem band_projected_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0 < c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W) ≤ c/2 → c/2≤C →
      topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : ℝ×ℝ → ℂ), Measurable f → Measurable g →
      MemLp f 2 planeMeasure → MemLp g 2 planeMeasure →
      Integrable f planeMeasure → Integrable g planeMeasure →
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0 < ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ)) ≤ m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      let I := verticalBinLabels ⌈C*W/w⌉₊ w W c C
      ‖finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
        (fun n : I => verticalBinCenter ⌈C*W/w⌉₊ W n)
        (fun z => field (planeCoordinates z))
        (fun n z => verticalConvolution
          (verticalProfileKernel verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)) f z)
        (verticalBinVector I ⌈C*W/w⌉₊ W g)‖≤
        A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
