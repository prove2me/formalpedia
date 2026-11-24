-- Prove2me | Theorems.Thm_GlobalTheory_Mem_ImagQuad_exists_imagQuad_integers
-- name    : GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:00.295609+00:00
-- url     : https://prove2.me/theorems/7147f179-ecee-4ecf-8965-86ade0300cc4
-- title:
--   Imag Quad: exists imag Quad integers
-- statement:
--   The Imag Quad construction uses the exists imag Quad integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsImagQuadIntegers.lean#L38-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsImagQuadIntegers.lean#L38-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.ImagQuad
open QuadraticZeta

theorem GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers : ∀ d : ℕ, d.Prime → d % 4 = 3 →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ω : 𝓞 K), IsTotallyComplex K ∧
      Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ (2 * ω - 1) ^ 2 = -(d : 𝓞 K) ∧
      (∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω) ∧
      ∀ a b : ℤ, Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2 := by sorry
