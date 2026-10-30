-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLatticePacket_reference_uniform_moments
-- name    : OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:54:06.315998+00:00
-- url     : https://prove2.me/theorems/0972a635-a8ae-4022-a795-b7d2cdff742e
-- title:
--   OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLatticePacket`, with `open MeasureTheory Set`, `open scoped BigOperators ENNReal FourierTransform`):
--
--   ```lean
--   theorem reference_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
--       (hlo : 0 < lo) (hhi : 0 ≤ hi) :
--       ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
--         [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
--         (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
--         (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
--         Monotone d →
--         (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
--         (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
--         ∀ (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
--         (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
--         let Q := P.referenceAnalyzedLine d v hv g hg hg1 y
--         (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
--           referenceSquareMomentCost (A/Real.pi^4) grid p*grid.lineMeasure univ ∧
--         (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
--           referenceVariationMomentCost M P.constant (A/Real.pi^4) grid p*grid.lineMeasure univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.LinePacketFamily`, `OAI.LipschitzHilbert.SourceLatticePacket`, `OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure`, `OAI.LipschitzHilbert.LinePacketFamily.squareFunction`, `OAI.LipschitzHilbert.LinePacketFamily.variation`, `OAI.LipschitzHilbert.SourceLatticePacket.constant`, `OAI.LipschitzHilbert.SourceLatticePacket.length`, `OAI.LipschitzHilbert.SourceLatticePacket.raw` and `OAI.LipschitzHilbert.SourceLatticePacket.referenceAnalyzedLine` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.SourceLatticePacket.referenceSquareMomentCost` and `OAI.LipschitzHilbert.SourceLatticePacket.referenceVariationMomentCost` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceReferenceBounds.lean (declaration OAI.LipschitzHilbert.SourceLatticePacket.reference_uniform_moments)

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
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem reference_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) →
      ∀ (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let Q := P.referenceAnalyzedLine d v hv g hg hg1 y
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        referenceSquareMomentCost (A/Real.pi^4) grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M P.constant (A/Real.pi^4) grid p*grid.lineMeasure univ := by
  sorry

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end
