-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_PacketRepresentation_exists_normalized_symbol_basic_l1
-- name    : OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:49:48.150652+00:00
-- url     : https://prove2.me/theorems/fc674059-1ae8-42af-8977-3ac34597f432
-- title:
--   OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1` of [lean/OAI/Analysis/LipschitzHilbert/Fourier/NormalizedSymbolBasicL1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/NormalizedSymbolBasicL1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.PacketRepresentation`, with `open Set MeasureTheory`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   theorem exists_normalized_symbol_basic_l1 (hVariation : LepingleInput)
--       (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (hq : 4≤q)
--       (A B cEta CEta a b Cprofile Csymbol : ℝ) (M order : ℕ)
--       (hA : 0≤A) (hB : 0≤B) (hcEta : 0 < cEta) (hCEta : 0≤CEta)
--       (ha : 0<a) (hb : 0<b) (haQuarter : a/2≤1/4)
--       (hCp : 0<Cprofile) (hCs : 0<Csymbol) (horder : 207≤order)
--       (hsmall : (2*Real.pi*A)/cEta<(a/2)/4)
--       (hcoverSmall : 6*max (2*b) ((2*Real.pi*A)/cEta+a/2)<1)
--       (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta (a/2) (2*b))
--       (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
--       (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
--       (hprofiles : ∀ nu : SymbolSpace,
--         planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤Cprofile ∧
--         planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤Cprofile) :
--       ∃ K : ℝ, 0<K ∧
--       ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
--         (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
--         0<w → w≤width → 0≤F →
--       ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
--         (∀ k, |2*Real.pi*center k|≤F/w) →
--         (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
--         (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
--         (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
--           (w/(topLength/(2:ℝ)^j.val)) M) →
--       ∀ (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ),
--         (∀ i k, symbolCoefficientBound (S i k) q≤Csymbol) →
--       ∀ (u : ℝ×ℝ → ℝ), Measurable u →
--       ∀ (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
--         (∀ k, Integrable (f k) planeMeasure) →
--         (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
--         (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
--       ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
--         (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
--         (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
--         ‖normalizedSymbolSumL1 chiA chiB (annularCutoff a b ha hb) topLength width w htop hwidth
--           labels theta center S u f g‖≤
--           K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.LepingleInput`, `OAI.LipschitzHilbert.planarProfileConstant`, `OAI.LipschitzHilbert.PacketLatticeData.OrdinaryModelNumerics`, `OAI.LipschitzHilbert.PacketRepresentation.planeMeasure` and `OAI.LipschitzHilbert.SourceSlopeLabels.LocalMultiplicity` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.PacketRepresentation.LatticeRow`, `OAI.LipschitzHilbert.PacketRepresentation.SymbolSpace`, `OAI.LipschitzHilbert.PacketRepresentation.analysisProfile`, `OAI.LipschitzHilbert.PacketRepresentation.annularCutoff`, `OAI.LipschitzHilbert.PacketRepresentation.planarInverseSchwartz`, `OAI.LipschitzHilbert.PacketRepresentation.symbolCoefficientBound` and `OAI.LipschitzHilbert.PacketRepresentation.synthesisProfile` (definitions bundle `OAIQ090A001` of this split); `OAI.LipschitzHilbert.PacketRepresentation.normalizedSymbolSumL1` (definitions bundle `OAIQ090A002` of this split).
--
--   **Used by.** The proofs of `OAI.LipschitzHilbert.PacketRepresentation.actual_sharp_band_measurable_restricted_log` and `OAI.LipschitzHilbert.PacketRepresentation.band_projected_high` of this split import it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Fourier/NormalizedSymbolBasicL1.lean (declaration OAI.LipschitzHilbert.PacketRepresentation.exists_normalized_symbol_basic_l1)

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
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem exists_normalized_symbol_basic_l1 (hVariation : LepingleInput)
    (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (hq : 4≤q)
    (A B cEta CEta a b Cprofile Csymbol : ℝ) (M order : ℕ)
    (hA : 0≤A) (hB : 0≤B) (hcEta : 0 < cEta) (hCEta : 0≤CEta)
    (ha : 0<a) (hb : 0<b) (haQuarter : a/2≤1/4)
    (hCp : 0<Cprofile) (hCs : 0<Csymbol) (horder : 207≤order)
    (hsmall : (2*Real.pi*A)/cEta<(a/2)/4)
    (hcoverSmall : 6*max (2*b) ((2*Real.pi*A)/cEta+a/2)<1)
    (num : PacketLatticeData.OrdinaryModelNumerics (2*Real.pi*A) cEta (a/2) (2*b))
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hchiB : ∀ z, chiB z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (hprofiles : ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile (planarInverseSchwartz chiA) q nu) (2*order)≤Cprofile ∧
      planarProfileConstant (analysisProfile (planarInverseSchwartz chiB) q nu) (2*order)≤Cprofile) :
    ∃ K : ℝ, 0<K ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) [Fintype κ]
      (topLength width w F : ℝ) (htop : 0<topLength) (hwidth : 0<width),
      0<w → w≤width → 0≤F →
    ∀ (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ),
      (∀ k, |2*Real.pi*center k|≤F/w) →
      (∀ k, cEta+(2*Real.pi*B)*(w/width)≤w*(2*Real.pi*center k)) →
      (∀ k, w*(2*Real.pi*center k)+(2*Real.pi*B)*(w/width)≤CEta) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (theta j)
        (w/(topLength/(2:ℝ)^j.val)) M) →
    ∀ (S : LatticeRow labels → κ → SchwartzMap SymbolSpace ℂ),
      (∀ i k, symbolCoefficientBound (S i k) q≤Csymbol) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (f : κ → ℝ×ℝ → ℂ) (fData g : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ k, Integrable (f k) planeMeasure) →
      (∀ z k, f k z=fData z k) → Measurable fData → Measurable g →
      (∀ z, ‖fData z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → fData z=0) →
      ‖normalizedSymbolSumL1 chiA chiB (annularCutoff a b ha hb) topLength width w htop hwidth
        labels theta center S u f g‖≤
        K*Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real E) := by
  sorry

end LipschitzHilbert.PacketRepresentation

end

end OAI
end
