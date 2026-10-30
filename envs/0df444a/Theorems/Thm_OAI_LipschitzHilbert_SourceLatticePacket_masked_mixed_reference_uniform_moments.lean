-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_SourceLatticePacket_masked_mixed_reference_uniform_moments
-- name    : OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:53:58.183296+00:00
-- url     : https://prove2.me/theorems/35f3bb8e-f638-47a0-b812-c067938981bc
-- title:
--   OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedPhysicalMoments.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedPhysicalMoments.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.SourceLatticePacket`, with `open MeasureTheory Set`, `open scoped ENNReal FourierTransform`):
--
--   ```lean
--   theorem masked_mixed_reference_uniform_moments (hVariation : LepingleInput)
--       {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
--       ∃ B M : ℝ, 0 < B ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
--         [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
--         (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
--         (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
--         (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
--         (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
--         (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
--         Monotone d →
--         (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
--           𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
--         (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
--           𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
--         (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
--           𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
--         (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
--           𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
--         ∀ (T : ∀ j, ι j → SlopeBox) (L A t cone : ℝ) (hL : 0 < L)
--           (hshort : ∀ j u, P.length j ≤ (T j u).length)
--           (hcone : ∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j)
--           (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo))
--           (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
--         (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
--         let rate := P.physicalReferenceMaskRate T L A t cone lo hL hshort hcone hsmall
--         let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
--         (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
--           referenceSquareMomentCost B grid p*grid.lineMeasure univ ∧
--         (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
--           referenceVariationMomentCost M (2*P.constant) B grid p*grid.lineMeasure univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.FiniteLineGrid`, `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.LinePacketFamily`, `OAI.LipschitzHilbert.SlopeBox`, `OAI.LipschitzHilbert.SourceLatticePacket`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure`, `OAI.LipschitzHilbert.LinePacketFamily.squareFunction`, `OAI.LipschitzHilbert.LinePacketFamily.variation`, `OAI.LipschitzHilbert.SourceLatticePacket.constant`, `OAI.LipschitzHilbert.SourceLatticePacket.frozenProfile`, `OAI.LipschitzHilbert.SourceLatticePacket.length`, `OAI.LipschitzHilbert.SourceLatticePacket.raw` and `OAI.LipschitzHilbert.SourceLatticePacket.withProfile` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.SlopeBox.maskLineA`, `OAI.LipschitzHilbert.SlopeBox.maskLineC`, `OAI.LipschitzHilbert.SourceLatticePacket.maskedMixedReferenceLine`, `OAI.LipschitzHilbert.SourceLatticePacket.physicalReferenceMaskRate`, `OAI.LipschitzHilbert.SourceLatticePacket.referenceSquareMomentCost` and `OAI.LipschitzHilbert.SourceLatticePacket.referenceVariationMomentCost` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceMaskedPhysicalMoments.lean (declaration OAI.LipschitzHilbert.SourceLatticePacket.masked_mixed_reference_uniform_moments)

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
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem masked_mixed_reference_uniform_moments (hVariation : LepingleInput)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ B M : ℝ, 0 < B ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      ∀ (T : ∀ j, ι j → SlopeBox) (L A t cone : ℝ) (hL : 0 < L)
        (hshort : ∀ j u, P.length j ≤ (T j u).length)
        (hcone : ∀ j u, |t-(T j u).slope| ≤ cone*(T j u).width/P.length j)
        (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo))
        (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let rate := P.physicalReferenceMaskRate T L A t cone lo hL hshort hcone hsmall
      let Q := P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y rate
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        referenceSquareMomentCost B grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M (2*P.constant) B grid p*grid.lineMeasure univ := by
  sorry

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end
