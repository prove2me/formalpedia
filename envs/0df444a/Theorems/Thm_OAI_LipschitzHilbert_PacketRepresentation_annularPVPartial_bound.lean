-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_annularPVPartial_bound
-- name    : OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:50:07.524226+00:00
-- url     : https://prove2.me/theorems/a06b9309-f181-42e7-a546-d34540f5ef30
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound` of [lean/OAI/Analysis/LipschitzHilbert/Fourier/AnnularPVPartialBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/AnnularPVPartialBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open MeasureTheory`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem annularPVPartial_bound (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
--       (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
--       (D : ℝ) (hD : 0≤D)
--       (hband : ∀ W : ℝ, 0<W → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
--         (∀ omega, planarFourier g omega≠0 → W*omega.2∈fixedAnnulus) →
--         MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure ∧
--         eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure≤
--           ENNReal.ofReal (D*‖g.toLp 2 planeMeasure‖))
--       (f : SchwartzMap (ℝ×ℝ) ℂ) :
--       MemLp (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
--         eLpNorm (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
--           ENNReal.ofReal (annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.planarFourier` and `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.planeCoordinates`, `OAI.LipschitzHilbert.PacketRepresentation.annularPVBoundConstant`, `OAI.LipschitzHilbert.PacketRepresentation.fixedAnnulus` and `OAI.LipschitzHilbert.PacketRepresentation.productSlopePrincipalValue` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial` (definitions bundle `OAIQ090A002` of this split); `OAI.LipschitzHilbert.Plane` (the published bundle `Def_LipschitzHilbert`).
--
--   **Used by.** The proofs of `OAI.LipschitzHilbert.main_of_three_published_inputs` and `OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs` of this split import it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/AnnularPVPartialBound.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.annularPVPartial_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002

section

attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem annularPVPartial_bound (N : ℕ) (field : Plane → ℝ) (hf : LipschitzWith 1 field)
    (hfb : ∀ z, |field z|≤1/4) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (D : ℝ) (hD : 0≤D)
    (hband : ∀ W : ℝ, 0<W → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
      (∀ omega, planarFourier g omega≠0 → W*omega.2∈fixedAnnulus) →
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R g) 2 planeMeasure≤
        ENNReal.ofReal (D*‖g.toLp 2 planeMeasure‖))
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
      eLpNorm (annularPVPartial N (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
        ENNReal.ofReal (annularPVBoundConstant D*‖f.toLp 2 planeMeasure‖) := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
