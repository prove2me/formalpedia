-- Prove2me | Theorems.Thm_GlobalTheory_GalMean_cover
-- name    : GlobalTheory.GalMean.cover
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:24.898008+00:00
-- url     : https://prove2.me/theorems/a1f5f0b5-ef59-4755-8f11-e89816fc7418
-- title:
--   Gal Mean: cover
-- statement:
--   The Gal Mean construction uses the cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L114-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L114-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open Classical

theorem GlobalTheory.GalMean.cover {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hE : Equidistributed φK j₀ 𝔞)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [IsGalois ℚ L] [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (hj : j₀ ∈ L)
    (hcard : 2 * (Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).card = Module.finrank ℚ L) :
    ∃ ext : (L →+* ℂ) → (ℂ ≃+* ℂ),
      (∀ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x),
        Fixes φK (ext τ) ∧ ∀ x : L, ext τ (x : ℂ) = τ x) ∧
      ∀ C : ClassGroup (𝓞 K), ((Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x)).filter
        (fun τ => ClassGroup.mk K (𝔞 (ext τ)) = C)).card * (2 * classNumber K) = Module.finrank ℚ L := by sorry
